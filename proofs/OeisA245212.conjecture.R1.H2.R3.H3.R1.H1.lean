import OMAReductions.R_OeisA245212_conjecture_R1_H2_R3_H3_R1




/-! An absolute exponent ceiling at the largest of three odd prime bases. -/

section

/- Exact interval certificates for the mixed 7-smooth A245212 family.
An absent upper endpoint represents the limit at an unbounded exponent. -/
namespace OMA.Smooth245212
open Finset

def Y (p : ℕ) : Option ℕ → ℚ
  | none => 0
  | some e => (((p:ℚ)⁻¹^(e+1)-1)/((p:ℚ)⁻¹-1))/(e+1)

def X (p : ℕ) (e : Option ℕ) : ℚ := 1+(1-Y p e)/((p:ℚ)-1)

theorem y_avg {p : ℕ} (hp : 1<p) (e : ℕ) :
    Y p (some e)=(∑ i ∈ range (e+1), (p:ℚ)⁻¹^i)/((e:ℚ)+1) := by
  rw [geom_sum_eq (x := (p:ℚ)⁻¹) (by
    have : (1:ℚ)<p := by exact_mod_cast hp
    exact (inv_lt_one_of_one_lt₀ this).ne)]; rfl

theorem y_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤Y p e := by
  cases e with
  | none => rfl
  | some e => rw [y_avg hp]; positivity

theorem y_anti {p : ℕ} (hp : 1<p) : Antitone (fun e : ℕ => Y p (some e)) := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have lp := (inv_lt_one_of_one_lt₀ pr).le
  have pos : 0≤(p:ℚ)⁻¹ := by positivity
  apply antitone_nat_of_succ_le
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_le_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) ≤ ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_le_sum (fun i hi => pow_le_pow_of_le_one pos lp (mem_range.mp hi).le)
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  nlinarith only [small]

theorem y_one {p : ℕ} (hp : 1<p) (e : Option ℕ) : Y p e ≤ 1 := by
  cases e with
  | none => norm_num [Y]
  | some e =>
    have h := y_anti hp (Nat.zero_le e)
    simpa [y_avg hp] using h

theorem x_nonneg {p : ℕ} (hp : 1<p) (e : Option ℕ) : 0≤X p e := by
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  have := sub_nonneg.mpr (y_one hp e)
  unfold X; positivity

structure Band where
  lo : ℕ
  hi : Option ℕ
  deriving DecidableEq

def Band.Contains (b : Band) (e : ℕ) := b.lo≤e ∧ ∀ h, b.hi=some h → e≤h

private theorem mono_range {p e : ℕ} (hp : 1<p) {b : Band} (h : b.Contains e) :
    Y p b.hi ≤ Y p (some e) ∧ Y p (some e) ≤ Y p (some b.lo) ∧
    X p (some b.lo) ≤ X p (some e) ∧ X p (some e) ≤ X p b.hi := by
  have le' : Y p b.hi ≤ Y p (some e) := by
    cases hh : b.hi with
    | none => exact y_nonneg hp _
    | some t => exact y_anti hp (h.2 t hh)
  have ge' := y_anti hp h.1
  have pr : (1:ℚ)<p := by exact_mod_cast hp
  exact ⟨le',ge',by unfold X; gcongr,by unfold X; gcongr⟩

abbrev I := Fin 4
abbrev Box := I → Band
def prime (i : I) : ℕ := ![2,3,5,7] i
theorem prime_lt (i : I) : 1 < prime i := by fin_cases i <;> decide

def score (e : I → ℕ) : ℚ :=
  (∏ i, X (prime i) (some (e i))) + ∏ i, Y (prime i) (some (e i))
def lower (b : Box) : ℚ :=
  (∏ i, X (prime i) (some (b i).lo)) + ∏ i, Y (prime i) (b i).hi
def upper (b : Box) : ℚ :=
  (∏ i, X (prime i) (b i).hi) + ∏ i, Y (prime i) (some (b i).lo)

theorem enclosure {b : Box} {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) :
    lower b ≤ score e ∧ score e ≤ upper b := by
  have v (i : I) := mono_range (prime_lt i) (h i)
  constructor
  · exact add_le_add
      (prod_le_prod (fun i _ => x_nonneg (prime_lt i) _) (fun i _ => (v i).2.2.1))
      (prod_le_prod (fun i _ => y_nonneg (prime_lt i) _) (fun i _ => (v i).1))
  · exact add_le_add
      (prod_le_prod (fun i _ => x_nonneg (prime_lt i) _) (fun i _ => (v i).2.2.2))
      (prod_le_prod (fun i _ => y_nonneg (prime_lt i) _) (fun i _ => (v i).2.1))

inductive Tree
| leaf
| split (i : I) (cut : ℕ) (left right : Tree)

def left (b : Box) (i : I) (cut : ℕ) : Box := Function.update b i ⟨(b i).lo, some cut⟩
def right (b : Box) (i : I) (cut : ℕ) : Box := Function.update b i ⟨cut+1, (b i).hi⟩
def Tree.check : Tree → Box → Bool
| .leaf,b => decide (2 < lower b ∨ upper b < 2)
| .split i cut l r,b => l.check (left b i cut) && r.check (right b i cut)

theorem Tree.sound (tree : Tree) {b : Box} (cert : tree.check b = true)
    {e : I → ℕ} (h : ∀ i,(b i).Contains (e i)) : score e ≠ 2 := by
  induction tree generalizing b with
  | leaf =>
    obtain pos|neg := of_decide_eq_true cert
    · exact ((enclosure h).1.trans_lt' pos).ne'
    · exact ((enclosure h).2.trans_lt neg).ne
  | split i cut l r il ir =>
    obtain ⟨cl,cr⟩ := Bool.and_eq_true_iff.mp cert
    by_cases ec : e i≤cut
    · apply il cl
      intro j; by_cases ji : j=i
      · subst j; simpa [left,Band.Contains] using And.intro (h i).1 ec
      · simpa [left,ji] using h j
    · apply ir cr
      intro j; by_cases ji : j=i
      · subst j; simpa [right,Band.Contains] using And.intro (by omega : cut+1≤e i) (h i).2
      · simpa [right,ji] using h j

end OMA.Smooth245212

end

section

/- Identification of the interval score with the original weighted sum. -/
namespace OMA.Smooth245212
open Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma Function

def W : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta
lemma w_mult : W.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
lemma w_apply (n : ℕ) : W n = ∑ d∈n.divisors, d*d.divisors.card := by
  rw [W,mul_zeta_apply]
  simp only [pmul_apply,id_apply,sigma_zero_apply]
lemma w_pow {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    W (p^e) = ∑ j ∈ range (e+1), p^j*(j+1) := by
  rw [w_apply,Nat.sum_divisors_prime_pow hp]
  simp [Nat.divisors_prime_pow hp]

private lemma weighted (p : ℚ) (e : ℕ) :
    (p-1)*(∑ j ∈ range (e+1), p^j*((j:ℚ)+1)) =
      ((e:ℚ)+1)*p^(e+1)-∑ j ∈ range (e+1), p^j := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,ih,pow_succ p (e+1)]
    push_cast; ring

theorem y_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    Y p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (σ 1 (p^e) : ℚ) := by
  have pn : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [y_avg hp.one_lt,sigma_one_apply_prime_pow hp]
  push_cast
  calc
    _ = ∑ j ∈ range (e+1), (p:ℚ)⁻¹^j*(p:ℚ)^e := by rw [←sum_mul]; field_simp
    _ = ∑ j ∈ range (e+1), (p:ℚ)^(e-j) := by
      refine sum_congr rfl fun j hj => ?_
      have add : j+(e-j)=e := by have := mem_range.mp hj; omega
      calc
        _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
        _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ pn),one_mul]
    _ = _ := by simpa using sum_range_reflect (fun j => (p:ℚ)^j) (e+1)

theorem x_factor {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)*(((e:ℚ)+1)*(p:ℚ)^e) = (W (p^e) : ℚ) := by
  have y := y_factor hp e
  rw [sigma_one_apply_prime_pow hp] at y
  push_cast at y
  rw [w_pow hp]; push_cast
  have pp : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have h := weighted (p:ℚ) e
  rw [pow_succ] at h
  dsimp [X]
  field_simp [sub_ne_zero.mpr pp.ne']
  linear_combination -h - y

theorem prime_prime (i : I) : Nat.Prime (prime i) := by fin_cases i <;> decide
theorem different : Function.Injective prime := by decide
def number (e : I → ℕ) := ∏ i, prime i^(e i)

section General
variable {ι : Type*} [Fintype ι] (p : ι → ℕ)
def total (e : ι → ℕ) : ℕ := ∏ i, p i^(e i)
private def tax (e : ι → ℕ) : ℚ := ∏ i, (((e i:ℕ):ℚ)+1)*(p i:ℚ)^(e i)
def normalized (e : ι → ℕ) : ℚ :=
  (∏ i, X (p i) (some (e i))) + ∏ i, Y (p i) (some (e i))

theorem normalized_of_eq (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (e : ι → ℕ) (heq : OeisA245212.a (total p e)=(σ 1 (total p e) : ℤ)) :
    normalized p e=2 := by
  classical
  let z (i : ι) := p i ^ (e i)
  have cop : (↑(univ : Finset ι) : Set ι).Pairwise (Coprime on z) := by
    intro i _ j _ h
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr
      (fun eq => h (hinj eq))).pow_left _).pow_right _
  have nz (i : ι) : z i ≠ 0 := pow_ne_zero _ (hp i).ne_zero
  have nn : total p e ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => nz i)
  have tot : W (total p e) = total p e*(total p e).divisors.card +
      ∑ d ∈ (total p e).properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d ∈ insert (total p e) (total p e).properDivisors, d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors nn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  have balanced : (W (total p e) : ℚ)+(σ 1 (total p e) : ℚ) =
      2*(total p e:ℚ)*(σ 0 (total p e) : ℚ) := by
    unfold OeisA245212.a at heq
    have ti : (W (total p e):ℤ) = (total p e:ℤ)*(total p e).divisors.card+
        ∑ d∈(total p e).properDivisors,(d:ℤ)*d.divisors.card := by exact_mod_cast tot
    rw [sigma_zero_apply]
    exact_mod_cast (by linarith : (W (total p e):ℤ)+(σ 1 (total p e):ℤ) =
      2*(total p e:ℤ)*(total p e).divisors.card)
  have wp := IsMultiplicative.map_prod z w_mult univ cop
  have sp := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ cop
  have tp := IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ cop
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (hp _)] at tp
  have factors : tax p e = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tax,prod_mul_distrib,tp,total]
    push_cast; ring
  have taxpos : 0<tax p e := by
    unfold tax
    exact prod_pos fun i _ => mul_pos (by positivity) (pow_pos (by exact_mod_cast (hp i).pos) _)
  apply mul_right_cancel₀ taxpos.ne'
  unfold normalized
  rw [add_mul,show (∏ i, X (p i) (some (e i)))*tax p e = (W (total p e):ℚ) by
    rw [tax,←prod_mul_distrib,wp]; push_cast
    exact prod_congr rfl fun i _ => x_factor (hp i) (e i),
    show (∏ i, Y (p i) (some (e i)))*tax p e = (σ 1 (total p e):ℚ) by
      rw [tax,←prod_mul_distrib,sp]; push_cast
      exact prod_congr rfl fun i _ => y_factor (hp i) (e i),factors]
  linarith only [balanced]

end General

theorem score_of_eq (e : I → ℕ)
    (heq : OeisA245212.a (number e)=(σ 1 (number e) : ℤ)) : score e=2 :=
  normalized_of_eq prime prime_prime different e heq

end OMA.Smooth245212

end

section

/- A uniform abundancy obstruction and the exclusion of constant
prime-exponent families in the A245212 divisor equality. -/
namespace OMA.Abundance245212
open OMA.Smooth245212 Finset ArithmeticFunction Nat
open scoped ArithmeticFunction.sigma

private theorem twice_weighted {p : ℕ} (hp : 1≤p) (e : ℕ) :
    (e+1)*(p^e+∑ i∈range (e+1),p^i) ≤
      2*(∑ i∈range (e+1),p^i*(i+1)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have bound : (∑ i∈range (e+1), p^i) ≤ (e+1)*p^e := by
      calc
        _ ≤ ∑ _i∈range (e+1),p^e := sum_le_sum (fun i hi =>
          Nat.pow_le_pow_right hp (by have := mem_range.mp hi; omega))
        _ = _ := by simp
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1)]
    linarith only [ih,bound]

theorem square_bound (n : ℕ) : (σ 0 n)^2*n*(σ 1 n) ≤ (W n)^2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    rw [sigma_zero_apply_prime_pow hp,sigma_one_apply_prime_pow hp,w_pow hp]
    have h := twice_weighted hp.pos e
    have hs := Nat.pow_le_pow_left h 2
    have am (u v : ℕ) : 4*u*v ≤ (u+v)^2 := by
      zify; nlinarith only [sq_nonneg ((u:ℤ)-v)]
    have haux := Nat.mul_le_mul_left ((e+1)^2) (am (p^e) (∑ i∈range (e+1),p^i))
    linarith only [haux,hs]
  | coprime a b _ _ cop ia ib =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop,
      isMultiplicative_sigma.map_mul_of_coprime cop,w_mult.map_mul_of_coprime cop]
    simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul ia ib

theorem balance {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : W n+σ 1 n=2*n*(σ 0 n) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  unfold OeisA245212.a at eq
  zify at total ⊢
  simp only [sigma_zero_apply]
  linarith

theorem sigma_lt {n : ℕ} (hn : n≠0)
    (eq : OeisA245212.a n=(σ 1 n:ℤ)) : σ 1 n<4*n := by
  have tpos : 0<σ 0 n := by
    rw [sigma_zero_apply,card_pos]; exact ⟨n,Nat.mem_divisors_self _ hn⟩
  have spos : 0<σ 1 n := by
    rw [sigma_one_apply]; exact sum_pos' (fun _ _ => by omega)
      ⟨n,Nat.mem_divisors_self _ hn,by omega⟩
  have bal := balance hn eq
  have ww : W n < 2*n*(σ 0 n) := by omega
  have strict := (square_bound n).trans_lt (Nat.pow_lt_pow_left ww (by decide : 2≠0))
  by_contra! ge
  have bad := Nat.mul_le_mul_left ((σ 0 n)^2*n) ge
  linarith only [bad,strict]

private theorem tau_gt_one {n : ℕ} (h : 1<n) : 1<σ 0 n := by
  rw [sigma_zero_apply]
  have hs : ({1,n}:Finset ℕ) ⊆ n.divisors := by
    intro d hd; simp only [mem_insert,mem_singleton] at hd
    rcases hd with rfl|rfl
    · exact one_mem_divisors.mpr (by omega)
    · exact mem_divisors_self _ (by omega)
  have := card_le_card hs
  have hc : 2≤n.divisors.card := by simpa [h.ne] using this
  omega

private theorem sigma_lt_twice_of_prime_tau (n : ℕ) :
    Nat.Prime (σ 0 n) → σ 1 n < 2*n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    intro ht; clear ht; rw [sigma_one_apply_prime_pow hp]
    induction e with
    | zero => simp
    | succ e ih =>
      rw [sum_range_succ _ (e+1),pow_succ]
      have hh := Nat.mul_le_mul_left (p^e) hp.two_le
      omega
  | coprime a b ha hb cop _ _ =>
    rw [isMultiplicative_sigma.map_mul_of_coprime cop]
    intro h
    rcases Nat.prime_mul_iff.mp h with ⟨_,h⟩|⟨_,h⟩
    · have := tau_gt_one hb; omega
    · have := tau_gt_one ha; omega

theorem no_resonance {m p : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (eq : OeisA245212.a m=(σ 1 m:ℤ)) (resonant : p*(σ 1 m)=2*m*(σ 0 m)) :
    p=2 ∧ m=1 := by
  by_cases p2 : p=2
  · subst p; refine ⟨rfl,?_⟩
    by_contra! more
    have s : σ 1 m < (σ 0 m)*m := by
      rw [sigma_one_apply,sigma_zero_apply]
      calc
        _ < ∑ _i∈m.divisors,m := sum_lt_sum
          (fun i hi => le_of_dvd (by omega) (dvd_of_mem_divisors hi))
          ⟨1,one_mem_divisors.mpr hm,by omega⟩
        _ = _ := by simp
    linarith only [s,resonant]
  · have p2nd : ¬p∣2 := fun h => p2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hdiv : p ∣ 2*m*(σ 0 m) := resonant ▸ dvd_mul_right _ _
    obtain ⟨k,hk⟩ := (hp.dvd_mul.mp hdiv).resolve_left
      (fun f => (hp.dvd_mul.mp f).elim p2nd cop)
    have can : p*(σ 1 m) = p*(2*m*k) := by rw [resonant,hk]; ring
    have sm := Nat.eq_of_mul_eq_mul_left hp.pos can
    have low := sigma_lt hm eq
    have tpos : 0<σ 0 m := by
      rw [sigma_zero_apply,Finset.card_pos]; exact ⟨m,mem_divisors_self _ hm⟩
    have k0 : 0<k := by by_contra! hz; simp [show k=0 by omega] at hk; omega
    have k1 : k=1 := by
      by_contra! h; have large := Nat.mul_le_mul_left (2*m) (show 2≤k by omega)
      linarith only [low,sm,large]
    rw [k1,mul_one] at hk sm
    have hlt := sigma_lt_twice_of_prime_tau m (hk ▸ hp)
    omega

theorem eq_of_balance {n : ℕ} (hn : n≠0) (bal : W n+σ 1 n=2*n*(σ 0 n)) :
    OeisA245212.a n=(σ 1 n:ℤ) := by
  have total : W n = n*n.divisors.card+∑ d∈n.properDivisors,d*d.divisors.card := by
    calc
      _ = ∑ d∈insert n n.properDivisors,d*d.divisors.card := by
        rw [Nat.insert_self_properDivisors hn,w_apply]
      _ = _ := sum_insert Nat.self_notMem_properDivisors
  rw [sigma_zero_apply] at bal
  unfold OeisA245212.a
  zify at total bal
  linarith

theorem affine_of_eq {p m e : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (W m:ℚ)*X p (some e)+(σ 1 m:ℚ)*Y p (some e)=2*m*(σ 0 m:ℚ) := by
  have cb := ((hp.coprime_iff_not_dvd.mpr cop).pow_left e).symm
  have bal := balance (mul_ne_zero hm (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime cb,isMultiplicative_sigma.map_mul_of_coprime cb,
    isMultiplicative_sigma.map_mul_of_coprime cb,sigma_zero_apply_prime_pow hp] at bal
  have cast : (W m:ℚ)*(W (p^e):ℚ)+(σ 1 m:ℚ)*(σ 1 (p^e):ℚ)=
      2*(m*(p:ℚ)^e)*((σ 0 m:ℚ)*((e:ℚ)+1)) := by exact_mod_cast bal
  have z : ((e:ℚ)+1)*(p:ℚ)^e ≠ 0 := mul_ne_zero (by positivity)
    (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
  apply mul_right_cancel₀ z
  rw [add_mul,mul_assoc,mul_assoc (σ 1 m:ℚ),x_factor hp e,y_factor hp e]
  linarith only [cast]

theorem y_strict {p : ℕ} (hp : 1<p) : StrictAnti (fun e : ℕ => Y p (some e)) := by
  have pp : (1:ℚ)<p := by exact_mod_cast hp
  have pos : 0<(p:ℚ)⁻¹ := by positivity
  have lt := inv_lt_one_of_one_lt₀ pp
  apply strictAnti_nat_of_succ_lt
  intro e
  simp only [y_avg hp,Nat.cast_add,Nat.cast_one]
  rw [sum_range_succ _ (e+1),div_lt_div_iff₀ (by positivity) (by positivity)]
  have small : (∑ _i ∈ range (e+1), (p:ℚ)⁻¹^(e+1)) < ∑ i∈range (e+1), (p:ℚ)⁻¹^i :=
    sum_lt_sum_of_nonempty (by simp) (fun _ hi =>
      pow_right_strictAnti₀ pos lt (mem_range.mp hi))
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at small
  linarith only [small]

theorem unique_exponent {p m e f : ℕ} (hm : m≠0) (hp : Nat.Prime p) (cop : ¬p∣m)
    (he : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ))
    (hf : OeisA245212.a (m*p^f)=(σ 1 (m*p^f):ℤ)) :
    e=f ∨ p=2 ∧ m=1 := by
  by_cases ef : e=f
  · exact Or.inl ef
  refine Or.inr ?_
  have ee := affine_of_eq hm hp cop he
  have ff := affine_of_eq hm hp cop hf
  have ne := (y_strict hp.one_lt).injective.ne ef
  have pp : (p:ℚ) ≠ 1 := by exact_mod_cast hp.ne_one
  unfold X at ee ff
  field_simp [sub_ne_zero.mpr pp] at ee ff
  have coeff : ((σ 1 m:ℚ)*((p:ℚ)-1)-(W m:ℚ)) *
      (Y p (some e)-Y p (some f))=0 := by linear_combination ee-ff
  have w := (mul_eq_zero.mp coeff).resolve_right (sub_ne_zero.mpr ne)
  have res : (p:ℚ)*(σ 1 m:ℚ)=2*m*(σ 0 m:ℚ) := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr pp)
    linear_combination ee+w*((p:ℚ)-Y p (some e))
  apply no_resonance hm hp cop _ (by exact_mod_cast res)
  apply eq_of_balance hm
  exact_mod_cast (show (W m:ℚ)+(σ 1 m:ℚ)=2*m*(σ 0 m:ℚ) by linarith only [w,res])

end OMA.Abundance245212

end

section

/- Every prime-power divisor of an A245212 solution divides a nonzero
combination of the two divisor moments of its coprime cofactor. -/
namespace OMA.PrimePowerDiv245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

theorem weighted {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p-1)*W (p^e)+σ 1 (p^e)=p*((e+1)*p^e) := by
  rw [w_pow hp,sigma_one_apply_prime_pow hp]
  induction e with
  | zero => simp; have := hp.one_lt; omega
  | succ e ih =>
    rw [sum_range_succ _ (e+1),sum_range_succ _ (e+1),mul_add,pow_succ]
    have add := Nat.sub_add_cancel (show 1≤p from hp.pos)
    nlinarith only [ih,congrArg (fun z:ℕ => z*(p^e*p)*(e+2)) add]

theorem power_divides {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (cop : m.Coprime p) (e : ℕ)
    (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (p:ℤ)^e ∣ (W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ) := by
  have van : (p:ZMod (p^e))^e=0 := by rw [←Nat.cast_pow]; exact ZMod.natCast_self _
  have w := congrArg (fun n : ℕ => (n:ZMod (p^e))) (weighted hp e)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_one,Nat.cast_pow,van,
    mul_zero] at w
  have s : ((p:ZMod (p^e))-1)*(σ 1 (p^e):ℕ) = -1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Nat.cast_sum,Nat.cast_pow]
    rw [mul_comm,geom_sum_mul,pow_succ,van,zero_mul,zero_sub]
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e)] at b
  have bb := congrArg (fun n : ℕ => (n:ZMod (p^e))) b
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,van,mul_zero,zero_mul] at bb
  rw [←Nat.cast_pow]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^e)).mp
  push_cast
  linear_combination ((p:ZMod (p^e))-1)^2*bb - (W m:ZMod (p^e))*((p:ZMod (p^e))-1)*w +
    ((W m:ZMod (p^e))-((p:ZMod (p^e))-1)*(σ 1 m:ZMod (p^e)))*s

theorem nonzero {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hp2 : p≠2)
    (cop : m.Coprime p) (e : ℕ) (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    (W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ)≠0 := by
  intro zero
  have same : W m=(p-1)*(σ 1 m) := by
    apply Nat.cast_inj (R:=ℤ) |>.mp
    push_cast [Nat.cast_sub hp.pos]; omega
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  rw [w_mult.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    isMultiplicative_sigma.map_mul_of_coprime (cop.pow_right e),
    sigma_zero_apply_prime_pow hp,same] at b
  have t := congrArg (fun v:ℕ => v*(σ 1 m)) (weighted hp e)
  have v : (p*(σ 1 m))*((e+1)*p^e)=(2*m*(σ 0 m))*((e+1)*p^e) := by
    nlinarith only [b,t]
  have res := Nat.eq_of_mul_eq_mul_right (show 0<(e+1)*p^e by have := hp.pos; positivity) v
  have mb : W m+σ 1 m=2*m*(σ 0 m) := by
    rw [←res,same]
    nlinarith only [congrArg (fun v:ℕ => v*(σ 1 m)) (Nat.sub_add_cancel hp.pos)]
  exact hp2 (no_resonance hm.ne' hp (hp.coprime_iff_not_dvd.mp cop.symm)
    (eq_of_balance hm.ne' mb) res).1

theorem cofactor_bound {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hp2 : p≠2)
    (cop : m.Coprime p) (e : ℕ) (eq : OeisA245212.a (m*p^e)=(σ 1 (m*p^e):ℤ)) :
    p^e ≤ ((W m:ℤ)-((p:ℤ)-1)*(σ 1 m:ℤ)).natAbs := by
  have d := power_divides hm hp cop e eq
  have nz := nonzero hm hp hp2 cop e eq
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr nz)
  simpa using Int.natAbs_dvd_natAbs.mpr d

end OMA.PrimePowerDiv245212

end

section

namespace OMA.ComplementaryLocal245212
open Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem moments {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p:ℤ)-1)*(σ 1 (p^e):ℤ)=p*(p:ℤ)^e-1 ∧
    ((p:ℤ)-1)^2*(W (p^e):ℤ)=p*((e+1)*(p-1)-1)*(p:ℤ)^e+1 := by
  have g : ((p:ℤ)-1)*(σ 1 (p^e):ℤ)=p*(p:ℤ)^e-1 := by
    rw [sigma_one_apply_prime_pow hp]
    push_cast
    rw [mul_comm ((p:ℤ)-1),geom_sum_mul,pow_succ,mul_comm]
  refine ⟨g,?_⟩
  have w := OMA.PrimePowerDiv245212.weighted hp e
  zify [Nat.cast_sub hp.pos] at w
  linear_combination ((p:ℤ)-1)*w-g

theorem binary (k : ℕ) :
    (σ 1 (2^k):ℤ)=(2:ℤ)^(k+1)-1 ∧ (W (2^k):ℤ)=1+k*(2:ℤ)^(k+1) := by
  have h := moments Nat.prime_two k
  norm_num at h
  rw [pow_succ]; constructor <;> nlinarith only [h.1,h.2]


end OMA.ComplementaryLocal245212

end

section

/- The divisor score strictly increases in one prime exponent as soon as
one other prime exponent is sufficiently large. -/
namespace OMA.CapOrder245212
open Finset OMA.Smooth245212 OMA.Abundance245212

private theorem geom (p : ℕ) (hp : 1<p) (e : ℕ) :
    (∑ i∈range (e+1),p^i)<2*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1),pow_succ]
    have := Nat.mul_le_mul_left (p^e) (show 2≤p from hp)
    omega

theorem y_short {q : ℕ} (hq : Nat.Prime q) (e : ℕ) :
    Y q (some e)*((e:ℚ)+1)<2 := by
  have h := y_factor hq e
  have l : (ArithmeticFunction.sigma 1 (q^e):ℚ)<2*(q:ℚ)^e := by
    exact_mod_cast (show ArithmeticFunction.sigma 1 (q^e)<2*q^e by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]; exact geom q hq.one_lt e)
  apply lt_of_mul_lt_mul_right (a:= (q:ℚ)^e)
  · linarith only [h,l]
  · positivity

private theorem x_one {q : ℕ} (hq : 1<q) (e : ℕ) : 1≤X q (some e) := by
  have q1 : (1:ℚ)<q := by exact_mod_cast hq
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (y_one hq _)) (by linarith))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def otherFactors (f : ι → ℚ) (i : ι) : ℚ := ∏ j∈univ.erase i,f j
private theorem update_value (p e : ι → ℕ) (i : ι) (t : ℕ) :
    normalized p (Function.update e i t) =
      otherFactors (fun j => X (p j) (some (e j))) i*X (p i) (some t) +
      otherFactors (fun j => Y (p j) (some (e j))) i*Y (p i) (some t) := by
  have prod_update (F : ι → ℕ → ℚ) :
      (∏ j,F j (Function.update e i t j))=otherFactors (fun j => F j (e j)) i * F i t := by
    rw [←prod_erase_mul _ _ (mem_univ i),Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.mp hj).1]
  exact congrArg₂ (·+·) (prod_update (fun j v => X (p j) (some v)))
    (prod_update (fun j v => Y (p j) (some v)))

theorem upward (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) (e : ι → ℕ)
    {i j : ι} (ij : j≠i) (high : 2*p i≤e j) {t : ℕ} (lt : e i<t) :
    normalized p e<normalized p (Function.update e i t) := by
  let xx := otherFactors (fun j => X (p j) (some (e j))) i
  let yy := otherFactors (fun j => Y (p j) (some (e j))) i
  have hj : j∈(univ:Finset ι).erase i := mem_erase.mpr ⟨ij,mem_univ j⟩
  have yl : yy≤Y (p j) (some (e j)) := by
    dsimp [yy,otherFactors]
    rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (hp j).one_lt _)
      (prod_le_one (fun h _ => y_nonneg (hp h).one_lt _) (fun h _ => y_one (hp h).one_lt _))
  have xl : 1≤xx := one_le_prod (fun h _ => x_one (hp h).one_lt _)
  have yr := y_short (hp j) (e j)
  have yp := y_nonneg (hp j).one_lt (some (e j))
  have pp : (1:ℚ)<p i := by exact_mod_cast (hp i).one_lt
  have ht : (2:ℚ)*p i≤e j := by exact_mod_cast high
  have cap : yy*((p i:ℚ)-1)<xx := by
    have bound := mul_le_mul_of_nonneg_right yl (show 0≤(p i:ℚ)-1 by linarith)
    have dual := mul_nonneg yp (show 0≤(e j:ℚ)+1-2*((p i:ℚ)-1) by linarith only [ht])
    linarith only [yr,bound,dual,xl]
  have dec := y_strict (hp i).one_lt lt
  have old : normalized p e=xx*X (p i) (some (e i))+yy*Y (p i) (some (e i)) := by
    simpa [xx,yy] using update_value p e i (e i)
  rw [old,update_value]
  change xx*X _ _+yy*Y _ _ < xx*X _ _+yy*Y _ _
  unfold X
  have positive := mul_pos (sub_pos.mpr cap) (sub_pos.mpr dec)
  apply sub_pos.mp
  have difference (a b : ℚ) :
      (xx*(1+(1-b)/((p i:ℚ)-1))+yy*b) - (xx*(1+(1-a)/((p i:ℚ)-1))+yy*a) =
      ((xx-yy*((p i:ℚ)-1))*(a-b))/((p i:ℚ)-1) := by
    field_simp [sub_ne_zero.mpr pp.ne']; ring
  rw [difference]
  exact div_pos positive (by linarith)

theorem nondecrease (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) {e f : ι → ℕ}
    (ef : e≤f) (witness : ∀ i,e i<f i → ∃ j,j≠i ∧ 2*p i≤e j) :
    normalized p e≤normalized p f := by
  let mix (s : Finset ι) (i : ι) := if i∈s then f i else e i
  have h (s : Finset ι) : normalized p e≤normalized p (mix s) := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s his ih =>
      have update : mix (insert i s)=Function.update (mix s) i (f i) := by
        funext j
        by_cases ji : j=i <;> simp [mix,ji]
      rw [update]
      have old : mix s i=e i := by simp [mix,his]
      rcases (ef i).eq_or_lt with same|lt
      · simpa [←same,←old] using ih
      · obtain ⟨j,ij,high⟩ := witness i lt
        have hj : e j ≤ mix s j := by by_cases js : j∈s <;> simp [mix,js,ef _]
        exact ih.trans (upward p hp (mix s) ij (high.trans hj) (old ▸ lt)).le
  simpa [mix] using h univ

theorem strict_of_changes (p : ι → ℕ) (hp : ∀ i,Nat.Prime (p i)) {e f : ι → ℕ}
    (ef : e≤f) {i : ι} (lt : e i<f i) (witness : ∀ i,e i<f i → ∃ j,j≠i ∧ 2*p i≤e j) :
    normalized p e<normalized p f := by
  let g := Function.update e i (f i)
  have eg (j : ι) : e j≤g j := by by_cases ji : j=i <;> simp [g,ji,ef _]
  have gf : g≤f := by intro j; by_cases ji : j=i <;> simp [g,ji,ef _]
  obtain ⟨j,ij,high⟩ := witness i lt
  refine (upward p hp e ij high lt).trans_le (nondecrease p hp (e:=g) gf ?_)
  intro l hl
  obtain ⟨r,rl,hr⟩ := witness l ((eg l).trans_lt hl)
  exact ⟨r,rl,hr.trans (eg r)⟩

end OMA.CapOrder245212

end

section

/- Cleared rational proxies for three independently moving odd prime powers. -/
namespace OMA.ThreeMovingLocal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

def den (p e : ℕ) (round : Bool) := if round then (e+1)*(p-1)^2 else e+1
def xn (p e : ℕ) (round : Bool) := if round then p*((e+1)*(p-1)-1) else e+1
def yn (p _e : ℕ) (round : Bool) := if round then p*(p-1) else 1
def xx (p e : ℕ) (b : Bool) : ℚ := (xn p e b:ℚ)/den p e b
def yy (p e : ℕ) (b : Bool) : ℚ := (yn p e b:ℚ)/den p e b

theorem den_pos {p : ℕ} (hp : 2≤p) (e) (b) : 0<den p e b := by
  have:0<p-1:=by omega
  cases b <;> simp [den]
  positivity

theorem quotients {p e : ℕ} (hp : p.Prime) :
    let u:ℚ:=(p:ℚ)-1
    let B:ℚ:=(e:ℚ)+1
    let P:ℚ:=(p:ℚ)^e
    let δ : ℚ:=1/(B*u^2*P)
    X p (some e) = xx p e true+δ ∧
    Y p (some e) = yy p e true-u*δ := by
  have p2:=hp.two_le
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have Bp : (0:ℚ)<(e:ℚ)+1:=by positivity
  have uu : (p-1)*(e+1)≥1:=Nat.mul_pos (by omega) (by omega)
  have uu' : 1≤(e+1)*(p-1):=by simpa [mul_comm] using uu
  have id:=OMA.ComplementaryLocal245212.moments hp e
  have w:((p:ℚ)-1)^2*W (p^e)=p*(((e:ℚ)+1)*(p-1)-1)*(p:ℚ)^e+1 := by exact_mod_cast id.2
  have s:((p:ℚ)-1)*σ 1 (p^e)=p*(p:ℚ)^e-1 := by exact_mod_cast id.1
  have x:=x_factor hp e
  have y:=y_factor hp e
  dsimp [xx,yy,xn,yn,den]
  push_cast [Nat.cast_sub hp.one_le,Nat.cast_sub uu']
  constructor
  · field_simp [sub_ne_zero.mpr pp.ne',Bp.ne',(show (0:ℚ)<p by positivity).ne']
    linear_combination ((p:ℚ)-1)^2*x+w
  · field_simp [sub_ne_zero.mpr pp.ne',Bp.ne',(show (0:ℚ)<p by positivity).ne']
    linear_combination ((p:ℚ)-1)*y+s

theorem bounds {p e m : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m) (sl : m≤e+1) (b : Bool) :
    1≤X p (some e) ∧ X p (some e)≤2 ∧ 0≤Y p (some e) ∧ Y p (some e)≤2/(m:ℚ) ∧
    1≤xx p e b ∧ xx p e b≤2 ∧ 0≤yy p e b ∧ yy p e b≤2/(m:ℚ) := by
  have pp : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have ep : (1:ℚ)≤e := by exact_mod_cast pe
  have md : (0:ℚ) < m := by exact_mod_cast mp
  have hl : (m:ℚ)≤(e:ℚ)+1 := by exact_mod_cast sl
  have bpos : (0:ℚ)<(e:ℚ)+1:=by positivity
  have ypos := y_nonneg hp.one_lt (some e)
  have ysm := y_one hp.one_lt (some e)
  have ub : Y p (some e)≤2/(m:ℚ) := (le_div_iff₀ md).mpr <|
    (mul_le_mul_of_nonneg_left hl ypos).trans (OMA.CapOrder245212.y_short hp e).le
  have xb : 1≤X p (some e) := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr ysm) (by linarith))
  have xb' : X p (some e)≤2 := by
    dsimp [X]
    suffices (1-Y p (some e))/((p:ℚ)-1)≤1 by linarith
    apply (div_le_one₀ (by linarith)).mpr;linarith
  refine ⟨xb,xb',ypos,ub,?_⟩
  cases b with
  | false =>
    have a0 : xx p e false=1 := by simp [xx,xn,den,bpos.ne']
    have b0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [a0,b0]
    refine ⟨by norm_num,by norm_num,by positivity,(div_le_div_iff₀ bpos md).mpr ?_⟩
    linarith
  | true =>
    have u : (0:ℚ)<(p:ℚ)-1:=by linarith
    have yw : yy p e true=(p:ℚ)/(((e:ℚ)+1)*(p-1)) := by
      dsimp [yy,yn,den];push_cast [Nat.cast_sub hp.one_le];field_simp
    have yw2 : yy p e true≤2/(m:ℚ) := by
      rw [yw,div_le_div_iff₀ (mul_pos bpos u) md]
      nlinarith only [mul_le_mul_of_nonneg_left hl (show (0:ℚ)≤p by positivity),
        mul_nonneg bpos.le (sub_nonneg.mpr pp)]
    have d0 : 0≤1/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e) := by positivity
    have one : 1≤xx p e true := by
      dsimp [xx,xn,den]
      push_cast [Nat.cast_sub hp.one_le,Nat.cast_sub (Nat.mul_pos (by omega : 0<e+1) (by have:=hp.two_le;omega : 0<p-1))]
      rw [le_div_iff₀ (mul_pos bpos (sq_pos_of_pos u)),one_mul]
      nlinarith only [mul_nonneg (sub_nonneg.mpr ep) u.le,pp]
    exact ⟨one,(by linarith only [(quotients hp (e:=e)).1,xb',d0]),by rw [yw];positivity,yw2⟩

theorem move {p e f g m k : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (small : b=true → 4*(p-1)<k*m^2)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (yl : y≤2/(m:ℚ)) (yl' : y'≤2/(m:ℚ)) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have cap0 := mul_le_mul yl yl' y1 (by positivity)
    have cap : (y*y')*(m:ℚ)^2≤4 := by
      apply (le_div_iff₀ (sq_pos_of_pos (show (0:ℚ) < m by exact_mod_cast mp))).mp
      convert cap0 using 1; ring
    have gate : 4*u < (k:ℚ)*m^2 := by
      have sc : (4:ℚ)*((p-1:ℕ):ℚ)<k*(m:ℚ)^2 := by exact_mod_cast small rfl
      simpa [u,Nat.cast_sub hp.one_le] using sc
    have unc : u*(y*y')<(k:ℚ) := by
      apply lt_of_mul_lt_mul_right (a:=(m:ℚ)^2) _ (by positivity)
      nlinarith only [gate,mul_le_mul_of_nonneg_left cap us]
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_lt_mul_of_pos_left unc g0,mul_le_mul_of_nonneg_left xl fm.le,fg]
    have q:=quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]

/-- A rounded factor costs at most 2/p^e; a base omitted to infinity
costs at most 2/p. Both local moments obey the same estimate. -/
theorem error {p e N : ℕ} (hp : p.Prime) (he : 0<e) (hN : 0<N) (b : Bool)
    (space : N ≤ (if b then p^e else p)) :
    |X p (some e)-xx p e b|≤2/(N:ℚ) ∧ |Y p (some e)-yy p e b|≤2/(N:ℚ) := by
  let u:ℚ:=(p:ℚ)-1
  let B:ℚ:=(e:ℚ)+1
  let P:ℚ:=(p:ℚ)^e
  have ulo : 1≤u := by dsimp [u];linarith only [show (2:ℚ)≤p by exact_mod_cast hp.two_le]
  have blo : 1≤B := by dsimp [B];linarith only [Nat.cast_nonneg (α:=ℚ) e]
  have up : 0<u := by linarith
  have bp : 0<B := by linarith
  have pp : 0<P := pow_pos (by exact_mod_cast hp.pos) _
  have np : (0:ℚ)<N := by exact_mod_cast hN
  let d:=1/(B*u^2*P)
  have dp : 0≤d := by dsimp [d];positivity
  have pairs:=quotients hp (e:=e)
  change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at pairs
  cases b with
  | true =>
    change N≤p^e at space
    have sg : (N:ℚ)≤P:=by dsimp [P];exact_mod_cast space
    have du : u*d=1/(B*u*P) := by dsimp [d];field_simp
    have ud : u*d≤2/(N:ℚ) := by
      rw [du,div_le_div_iff₀ (by positivity) np]
      have big : P≤B*u*P := le_mul_of_one_le_left pp.le (one_le_mul_of_one_le_of_one_le blo ulo)
      linarith
    rw [pairs.1,pairs.2,add_sub_cancel_left,sub_sub_cancel_left,abs_neg,abs_of_nonneg dp,abs_of_nonneg (mul_nonneg up.le dp)]
    exact ⟨(le_mul_of_one_le_left dp ulo).trans ud,ud⟩
  | false =>
    change N≤p at space
    have small : (N:ℚ)≤2*u := by
      have pp : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
      dsimp [u];linarith only [pp,show (N:ℚ)≤p by exact_mod_cast space]
    have frac : 1/u ≤ 2/(N:ℚ):= (div_le_div_iff₀ up np).mpr (by linarith)
    have xr:= (bounds hp he (by decide : 0<1) (by omega) false).1
    have xe : X p (some e)-1≤1/u := by dsimp [X,u];rw [add_sub_cancel_left];gcongr;exact sub_le_self _ (y_nonneg hp.one_lt _)
    have yupper : yy p e true-1/B=1/(B*u) := by
      dsimp [yy,yn,den,u,B];push_cast [Nat.cast_sub hp.one_le];field_simp [show (p:ℚ)-1≠0 from up.ne'];ring
    have lower : 1/B≤Y p (some e) := by
      apply (div_le_iff₀ bp).mpr
      apply le_of_mul_le_mul_right (a:=P) _ pp
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      dsimp [B,P];nlinarith only [y_factor hp e,big]
    have pre : Y p (some e)-1/B≤1/(B*u) := by
      nlinarith only [pairs.2,yupper,mul_nonneg up.le dp]
    have s : 1/(B*u) ≤ 1/u := one_div_le_one_div_of_le up (le_mul_of_one_le_left up.le blo)
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/B := by simp [yy,yn,den,B]
    rw [xx0,yy0,abs_of_nonneg (sub_nonneg.mpr xr),abs_of_nonneg (sub_nonneg.mpr lower)]
    exact ⟨xe.trans frac,pre.trans (s.trans frac)⟩

end OMA.ThreeMovingLocal245212

end

section

/- Every prefix of three signed, rounded local moments is separated if
its shortest length squared dominates its longest length relative to k. -/
namespace OMA.ThreeMovingGap245212
open Nat Finset OMA.Smooth245212 OMA.ThreeMovingLocal245212

structure Family where
  p : Fin 3→ℕ
  e : Fin 3→ℕ
  k : ℕ
  m : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 0<k
  mp : 0 < m
  lengths : ∀i,m≤e i+1 ∧ e i+1≤L
  comparable : 4*max k L < k*m^2

def exactX (c : Family) (i : Fin 3) := X (c.p i) (some (c.e i))
def exactY (c : Family) (i : Fin 3) := Y (c.p i) (some (c.e i))
def x' (c : Family) (b : Fin 3→Bool) (i : Fin 3) := xx (c.p i) (c.e i) (b i)
def y' (c : Family) (b : Fin 3→Bool) (i : Fin 3) := yy (c.p i) (c.e i) (b i)
def dust (c : Family) (b : Fin 3→Bool) := ∏i,den (c.p i) (c.e i) (b i)
def NX (c : Family) (b : Fin 3→Bool) := ∏i,xn (c.p i) (c.e i) (b i)
def NY (c : Family) (b : Fin 3→Bool) := ∏i,yn (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin 3→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family) (b : Fin 3→Bool) : 0<dust c b :=
  prod_pos (fun i _=>den_pos (c.prime i).two_le _ _)

theorem clear (c : Family) (b : Fin 3→Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x',xx];push_cast;rw [←prod_mul_distrib]
    apply prod_congr rfl;intro i _
    exact div_mul_cancel₀ _ (by exact_mod_cast (den_pos (c.prime i).two_le (c.e i) (b i)).ne')
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y',yy];push_cast;rw [←prod_mul_distrib]
    apply prod_congr rfl;intro i _
    exact div_mul_cancel₀ _ (by exact_mod_cast (den_pos (c.prime i).two_le (c.e i) (b i)).ne')
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s

private theorem descend (c : Family) (b : Fin 3→Bool) (f g : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (small : ∀i,b i=true → c.p i≤ max (c.k+1) c.L) :
    score f g (x' c b) (y' c b)<score f g (exactX c) (exactY c) := by
  let mix (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactY c i else y' c b i
  have adv (s : Finset (Fin 3)) {i} (fresh : i∉s) :
      score f g (mix s) (miy s)<score f g (mix (insert i s)) (miy (insert i s)) := by
    let all j:=bounds (c.prime j) (c.positive j) c.mp (c.lengths j).1 (b j)
    have xpos s j : 1≤ mix s j := by
      dsimp [mix];split <;> first | exact (all j).1 | exact (all j).2.2.2.2.1
    have ylo s j : 0≤ miy s j := by
      dsimp [miy];split <;> first | exact (all j).2.2.1 | exact (all j).2.2.2.2.2.2.1
    have yhi s j : miy s j≤2/(c.m:ℚ) := by
      dsimp [miy];split <;> first | exact (all j).2.2.2.1 | exact (all j).2.2.2.2.2.2.2
    have single {j l : Fin 3} (n : j≠i) (n' : l≠i) :
        (f:ℚ)*mix s i*mix s j*mix s l+g*miy s i*miy s j*miy s l <
        f*mix (insert i s) i*mix (insert i s) j*mix (insert i s) l+
          g*miy (insert i s) i*miy (insert i s) j*miy (insert i s) l := by
      have size (inb : b i=true) : 4*(c.p i-1)<c.k*c.m^2 := by
        have lim:=small i inb
        have before : c.p i-1≤ max c.k c.L := by omega
        exact (Nat.mul_le_mul_left _ before).trans_lt c.comparable
      have step:=move (c.prime i) (c.positive i) c.mp c.kp gp fg (b i) size
        (mix s j) (mix s l) (miy s j) (miy s l) (xpos s j) (xpos s l) (ylo s j) (ylo s l) (yhi s j) (yhi s l)
      simpa [mix,miy,exactX,exactY,x',y',fresh,n,n'] using step
    dsimp [score]
    simp only [Fin.prod_univ_three]
    have choice : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choice with rfl|rfl|rfl
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=1) (l:=2) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=2) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=1) (by decide) (by decide)
  have a:=adv ∅ (i:=0) (by decide)
  have b1:=adv {0} (i:=1) (by decide)
  have d:=adv {1,0} (i:=2) (by decide)
  have endset : insert (2:Fin 3) ({1,0}:Finset (Fin 3))=univ := by decide
  simpa [mix,miy,endset] using (a.trans b1).trans d

private theorem largest {c : Family} {b : Fin 3→Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=xn (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>xn (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=yn (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>yn (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:= (c.lengths i').2
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    dsimp [den] at v
    split at v
    next on =>
      have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,on⟩
      have sz:=top i' mt
      rcases pr.dvd_mul.mp v with bad|bad
      · exact absent bad
      · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
          (by omega) (pr.dvd_of_dvd_pow bad)
    next off => exact absent v

theorem nonzero (c : Family) (b : Fin 3→Bool) (f g l : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (frac : f+g=(c.k+1)*l) (unit : ∀i,¬c.p i∣l)
    (actual : score f g (exactX c) (exactY c)≤(f+g:ℕ)) :
    (f+g)*dust c b ≠ f*NX c b+g*NY c b := by
  intro hit
  have less:=(descend c b f g gp fg (largest frac unit hit)).trans_le actual
  have val:=clear c b f g
  have id : ((f+g:ℕ):ℚ)*dust c b=((f*NX c b+g*NY c b:ℕ):ℚ) := by exact_mod_cast hit
  exact (ne_of_lt (mul_lt_mul_of_pos_right less (show (0:ℚ)<dust c b by exact_mod_cast dust_pos c b))) (val.trans id.symm)

end OMA.ThreeMovingGap245212

end

section

/- Integer size comparisons for the general complementary-exponent bound. -/
namespace OMA.ComplementarySize245212

/-- An elementary integer substitute for d log b ≤ b/2 when
b≥16(d+1)². -/
theorem absorb {b d : ℕ} (big : 16*(d+1)^2≤b) : b^(2*d)≤2^b := by
  let s := b.sqrt
  have sl : (4*(d+1)) ≤ s := Nat.le_sqrt'.mpr (by nlinarith only [big])
  have slo : s^2≤b := Nat.sqrt_le' b
  have shi : b<(s+1)^2 := Nat.lt_succ_sqrt' b
  have bas : b≤2^(2*s) := calc
    _ ≤ 2*s^2+1 := by
      nlinarith only [shi, Nat.mul_le_mul_left s (show 2 ≤ s by omega)]
    _ ≤ _ := Nat.two_mul_sq_add_one_le_two_pow_two_mul s
  calc
    _ ≤ (2^(2*s))^(2*d) := Nat.pow_le_pow_left bas _
    _ = _ := (pow_mul _ _ _).symm
    _ ≤ 2^b := Nat.pow_le_pow_right (by decide)
      (by nlinarith only [slo,Nat.mul_le_mul_left s sl])

/-- Common last step, using the integer-only growth estimate above. -/
theorem exponents {a d K : ℕ} (hK : 1≤K)
    (power : 2^(a-1)≤2^(16*(d+1)^2)*(2^K)^(d+1)*(a+1)^d*K^(3*d+1)) :
    a+1≤64*(d+1)^2*K := by
  by_cases big : 16*(d+1)^2≤a+1
  · let X := 16*(d+1)^2 + K*(d+1) + K*(3*d+1)
    have scale : K≤(2:ℕ)^K := (Nat.lt_pow_self (by decide : 1<2)).le
    have idpow : 2^X = (2^(16*(d+1)^2)*(2^K)^(d+1))*(2^K)^(3*d+1) := by
      dsimp [X]
      rw [pow_add (2:ℕ) (16*(d+1)^2+K*(d+1)) (K*(3*d+1)),
        pow_add (2:ℕ) (16*(d+1)^2) (K*(d+1)),pow_mul (2:ℕ) K (d+1),
        pow_mul (2:ℕ) K (3*d+1)]
    have input : 2^(a-1)≤2^X*(a+1)^d := calc
      _ ≤ _ := power
      _ ≤ 2^(16*(d+1)^2)*(2^K)^(d+1)*(a+1)^d*(2^K)^(3*d+1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left scale _)
      _ = _ := by
        rw [idpow]
        exact mul_right_comm _ _ _
    have hh := Nat.pow_le_pow_left input 2
    rw [←pow_mul,mul_pow,←pow_mul,←pow_mul] at hh
    have v := Nat.mul_le_mul_left (2^(X*2)) (absorb big)
    rw [Nat.mul_comm 2 d] at v
    rw [←pow_add] at v
    have hb := (pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp (hh.trans v)
    dsimp [X] at hb
    have al : 1≤a := by nlinarith only [big, Nat.zero_le d, Nat.zero_le (d^2)]
    have cut := Nat.sub_add_cancel al
    nlinarith only [hb,cut,
      Nat.mul_le_mul_right ((d+1)^2) hK,
      Nat.zero_le (K*d),Nat.zero_le (K*d^2),hK]
  · nlinarith only [Nat.lt_of_not_ge big, Nat.mul_le_mul_right ((d+1)^2) hK]

end OMA.ComplementarySize245212

end

section

/- Integer growth estimates and an empty multiplicative interval for three bases. -/
namespace OMA.ThreeMovingScalar245212

def cut (x j : ℕ) := x^(16^j)

theorem cut_succ (x i : ℕ) : cut x (i+1)=(cut x i)^16 := by
  rw [cut,cut,pow_succ,pow_mul]

theorem cut_mono {x : ℕ} (pos : 1≤x) : Monotone (cut x) :=
  fun _ _ le=>Nat.pow_le_pow_right pos (Nat.pow_le_pow_right (by decide) le)

theorem empty_interval (x : ℕ) (hx : 1≤x) (p : Fin 3→ℕ) :
    ∃j : Fin 4,∀i, p i ≤ cut x j.val ∨ cut x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have:=Fintype.card_le_of_injective _ inj
  norm_num at this

def budget := 16^4

def base (k L : ℕ) := 128*(k+2)*(L+1)

-- The larger exponent covers substitution of the exact dyadic numerator.
def degree := (budget+4)*budget

def minimumCut := 64*(degree+1)^2

private theorem square_product (p m F : ℕ) : ((p^14*m^2)^F)^2=p^(28*F)*m^(4*F) := by
  rw [←pow_mul,mul_pow,←pow_mul,←pow_mul,show 14*(F*2)=28*F by ring,show 2*(F*2)=4*F by ring]

theorem scale {m k L p e : ℕ} (hp : 3≤p) (hk : k<2*p) (hm : minimumCut ≤ m)
    (comparable : L ≤ k*m^2) (low : m≤e+1) :
    (base k L)^degree ≤ p^e := by
  let F:=degree
  have fp : 1≤F := by decide
  change 64*(F+1)^2≤ m at hm
  have mp : 1≤ m:=by nlinarith only [hm,Nat.zero_le (F^2),Nat.zero_le F]
  have pp : 1≤p:=by omega
  have kcap : k+2≤4*p := by omega
  have Lcap : L+1≤3*p*m^2 := by
    have mpos:=Nat.mul_pos (show 0<p by omega) (pow_pos mp 2)
    nlinarith only [comparable,Nat.mul_le_mul_right (m^2) hk.le,mpos]
  have scale : base k L≤p^14*m^2 := by
    have sixteen : 1536≤p^12 := (by decide : 1536≤3^12).trans (Nat.pow_le_pow_left hp _)
    have b:=Nat.mul_le_mul kcap Lcap
    dsimp [base]
    nlinarith only [Nat.mul_le_mul_left 128 b,Nat.mul_le_mul_right (p^2*m^2) sixteen]
  have grow := OMA.ComplementarySize245212.absorb (d:=2*F) (b:=m) (by nlinarith only [hm,Nat.zero_le F])
  have poly : m^(4*F)≤p^m := (by convert grow using 1; ring : m^(4*F)≤2^m).trans (Nat.pow_le_pow_left (by omega) _)
  have gain : 28*F+m≤2*e := by
    nlinarith only [hm,low,Nat.zero_le (F^2)]
  apply (pow_le_pow_iff_left₀ (show 0≤(base k L)^degree from Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
  change ((base k L)^F)^2≤(p^e)^2
  calc
    _ ≤ ((p^14*m^2)^F)^2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left scale _) _
    _ = p^(28*F)*m^(4*F) := square_product p m F
    _ ≤ p^(28*F)*p^m := Nat.mul_le_mul_left _ poly
    _ = p^(28*F+m) := (pow_add ..).symm
    _ ≤ p^(2*e) := Nat.pow_le_pow_right pp gain
    _ = (p^e)^2 := by rw [mul_comm,pow_mul]

end OMA.ThreeMovingScalar245212

end

section

/- An explicit uniform distance from a rational target to Euler products
of bounded length, provided none of their subproducts hits the target. -/
namespace OMA.CofactorEulerSeparation245212
open Finset Nat

def num (s : Finset ℕ) := ∏p∈s,p
def den (s : Finset ℕ) := ∏p∈s,(p-1)
def gap (A H : ℕ) (s : Finset ℕ) := ((A:ℤ)*num s-(H:ℤ)*den s).natAbs
def miss (A H : ℕ) (s : Finset ℕ) := ∀t⊆s,A*num t≠H*den t

def budget (A : ℕ) : ℕ→ℕ
  | 0=>1
  | r+1=>let b:=budget A r;max (2*b) ((2+2*A*2^r*b)^(r+1))

private theorem budget_pos (A r : ℕ) : 0<budget A r := by
  induction r with
  | zero=>simp [budget]
  | succ r ih=>exact (Nat.mul_pos (by decide) ih).trans_le (le_max_left _ _)

private theorem gap_pos {A H : ℕ} {s : Finset ℕ} (m : A*num s≠H*den s) : 0<gap A H s := by
  apply Int.natAbs_pos.mpr
  intro z
  exact m (by exact_mod_cast sub_eq_zero.mp z)

private theorem size {s : Finset ℕ} (positive : ∀p∈s,2≤p) : num s≤2^s.card*den s := by
  calc
    num s ≤ ∏p∈s,(2*(p-1)) := by
      apply prod_le_prod'
      intro p mem;have:=positive p mem;omega
    _ = _ := by simp [den,prod_mul_distrib]

private theorem spread {u x z : ℤ} (u0 : 0≤u) (x0 : 0≤x) (large : 2*x≤u*|z|) :
    u*|z|≤2*|u*z+x| := by
  have tri:=abs_add_le (u*z+x) (-x)
  rw [add_neg_cancel_right,abs_mul,abs_of_nonneg u0,abs_neg,abs_of_nonneg x0] at tri
  linarith

theorem separated (A H K : ℕ) (s : Finset ℕ) (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) : den s≤budget A K*gap A H s := by
  classical
  induction K generalizing s with
  | zero=>
    have empty : s=∅:=card_eq_zero.mp (by omega)
    subst s
    simpa [den,budget] using Nat.succ_le_of_lt (gap_pos (apart ∅ (by simp)))
  | succ K ih=>
    by_cases empty : s=∅
    · subst s
      simpa [den] using Nat.succ_le_of_lt (Nat.mul_pos (budget_pos A (K+1)) (gap_pos (apart ∅ (by simp))))
    have nonempty:=nonempty_iff_ne_empty.mpr empty
    let q:=s.max' nonempty
    have mem : q∈s:=s.max'_mem _
    have qp:=positive q mem
    let t:=s.erase q
    have sub : t⊆s:=erase_subset _ _
    have oldBound:=ih t (by dsimp [t];rw [card_erase_of_mem mem];omega)
      (fun p hp=>positive p (sub hp)) (fun z hz=>apart z (hz.trans sub))
    have scale:=size (s:=t) (fun p hp=>positive p (sub hp))
    have tc : t.card≤K := by dsimp [t];rw [card_erase_of_mem mem];omega
    let B:=budget A K
    have U : num s=q*num t := (mul_prod_erase s (fun p=>p) mem).symm
    have V : den s=(q-1)*den t := (mul_prod_erase s (fun p=>p-1) mem).symm
    by_cases large : 2*A*2^K*B≤q-1
    · have twice : 2*A*num t≤(q-1)*gap A H t := by
        calc
          _ ≤ 2*A*(2^K*(B*gap A H t)) := Nat.mul_le_mul_left _ (scale.trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) tc) oldBound))
          _ = (2*A*2^K*B)*gap A H t := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ large
      have twiceInt : 2*((A:ℤ)*num t)≤((q-1:ℕ):ℤ)*|(A:ℤ)*num t-(H:ℤ)*den t| := by
        have cast:=Int.ofNat_le.mpr twice
        simpa only [gap,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs,mul_assoc] using cast
      have pre:=spread (u:=((q-1:ℕ):ℤ)) (x:=(A:ℤ)*num t) (z:=(A:ℤ)*num t-(H:ℤ)*den t)
        (by positivity) (by positivity) twiceInt
      have id : ((q-1:ℕ):ℤ)*((A:ℤ)*num t-(H:ℤ)*den t)+A*num t=(A:ℤ)*num s-(H:ℤ)*den s := by
        rw [U,V];push_cast [Nat.cast_sub (show 1≤q by omega)];ring
      rw [id] at pre
      have control : (q-1)*gap A H t≤2*gap A H s := by
        apply Int.ofNat_le.mp
        simpa [gap,Int.natCast_natAbs] using pre
      calc
        den s ≤ (q-1)*(B*gap A H t) := V ▸ Nat.mul_le_mul_left _ oldBound
        _ = B*((q-1)*gap A H t) := by ring
        _ ≤ B*(2*gap A H s) := Nat.mul_le_mul_left _ control
        _ = (2*B)*gap A H s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
    · let J:=2+2*A*2^K*B
      have lo : 0<J := by dsimp [J];omega
      have modest : den s≤J^(K+1) := by
        refine (prod_le_pow_card s (fun p=>p-1) J ?_).trans (Nat.pow_le_pow_right lo card)
        intro p hp
        have below : p≤q:=s.le_max' p hp
        dsimp [J];omega
      have nonzero := gap_pos (apart s (Subset.rfl))
      exact modest.trans ((le_max_right _ _).trans (Nat.le_mul_of_pos_right _ nonzero))


theorem miss_odd {A H : ℕ} {s : Finset ℕ} (oa : Odd A) (eh : Even H)
    (pr : ∀p∈s,Odd p) : miss A H s := by
  intro t ht eqn
  have all (u : Finset ℕ) (ho : ∀p∈u,Odd p) : Odd (num u) := by
    induction u using Finset.induction_on with
    | empty=>simp [num]
    | @insert p u fresh ih=>
      rw [num,prod_insert fresh]
      exact (ho p (mem_insert_self ..)).mul (ih (fun q hq=>ho q (mem_insert_of_mem hq)))
  have left:=oa.mul (all t (fun p hp=>pr p (ht hp)))
  rw [eqn] at left
  exact (Nat.not_even_iff_odd.mpr left) (eh.mul_right _)

theorem miss_avoids {A H : ℕ} {s : Finset ℕ} (different : A≠H)
    (pr : ∀p∈s,p.Prime) (avoid : ∀p∈s,¬p∣H) : miss A H s := by
  intro t ht eqn
  by_cases empty : t=∅
  · exact different (by simpa [empty,num,den] using eqn)
  have nonempty:=nonempty_iff_ne_empty.mpr empty
  let q:=t.max' nonempty
  have mq : q∈t:=t.max'_mem _
  have pq:=pr q (ht mq)
  have dvd : q∣H*den t := eqn ▸ dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p=>p) mq) A
  rcases pq.dvd_mul.mp dvd with bad|denom
  · exact avoid q (ht mq) bad
  obtain ⟨p,mp,dv⟩:=(pq.prime.dvd_finsetProd_iff (fun j=>j-1)).mp denom
  have upper : p≤q:=t.le_max' _ mp
  have lower:=(pr p (ht mp)).one_lt
  have:=Nat.le_of_dvd (show 0<p-1 by omega) dv
  omega

/-- A computable absolute gap, uniform over all allowed support sets. -/
theorem rational_gap {A H K : ℕ} {s : Finset ℕ} (card : s.card≤K)
    (positive : ∀p∈s,2≤p) (apart : miss A H s) :
    1 ≤ (budget A K:ℚ)*|(A:ℚ)*((num s:ℚ)/den s)-H| := by
  have n:=separated A H K s card positive apart
  have dp : 0<den s := prod_pos (fun p hp=>by have:=positive p hp;omega)
  have v : (0:ℚ)<den s := by exact_mod_cast dp
  let u : ℤ:=(A:ℤ)*num s-(H:ℤ)*den s
  have cast : (den s:ℚ)≤(budget A K:ℚ)*|(u:ℚ)| := by
    have intBound:=Int.ofNat_le.mpr n
    simp only [gap,Nat.cast_mul,Int.natCast_natAbs] at intBound
    dsimp [u]
    exact_mod_cast intBound
  have eqn : ((A:ℚ)*((num s:ℚ)/den s)-H)*(den s:ℚ)=(u:ℚ) := by
    dsimp [u];push_cast;field_simp
  apply (mul_le_mul_iff_of_pos_right v).mp
  have ab:=congrArg (fun z:ℚ=>|z|) eqn
  rw [abs_mul,abs_of_pos v] at ab
  simpa only [one_mul,mul_assoc,ab] using cast

end OMA.CofactorEulerSeparation245212

end

section

/- Finite original A245212 solutions of bounded odd-prime rank
when no odd prime divides another exponent length or the divisor count
of the fixed cofactor. -/
namespace OMA.CofactorCrossOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

private theorem sigma_bound {h : ℕ} (pos : 0<h) : σ 1 h≤h*σ 0 h := by
  rw [sigma_one_apply,sigma_zero_apply,mul_comm]
  simpa using (sum_le_card_nsmul h.divisors (fun d : ℕ=>d) h (fun d hd=>
    Nat.le_of_dvd pos (Nat.mem_divisors.mp hd).1))

theorem normalized_extension {ι : Type*} [Fintype ι] {h : ℕ} {p e : ι→ℕ} (hh : 0<h) (pr : ∀i,(p i).Prime)
    (unique : Function.Injective p) (cop : ∀i,h.Coprime (p i))
    (eqn : OeisA245212.a (h*total p e)=(σ 1 (h*total p e):ℤ)) :
    ((W h:ℚ)/(h*σ 0 h:ℕ))*(∏i,X (p i) (some (e i)))+
      ((σ 1 h:ℚ)/(h*σ 0 h:ℕ))*(∏i,Y (p i) (some (e i)))=2 := by
  classical
  let z (i : ι):=p i^e i
  have pair : (↑(univ : Finset ι) : Set ι).Pairwise (fun i j=>(z i).Coprime (z j)) := by
    intro i _ j _ different
    exact (((coprime_primes (pr i) (pr j)).mpr (fun same=>different (unique same))).pow_left _).pow_right _
  have hc : h.Coprime (total p e) := coprime_prod_right_iff.mpr (fun i _=>(cop i).pow_right _)
  have nz : total p e≠0 := prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (pr i).ne_zero)
  have bal:=OMA.Abundance245212.balance (mul_ne_zero hh.ne' nz) eqn
  rw [w_mult.map_mul_of_coprime hc,isMultiplicative_sigma.map_mul_of_coprime hc,
    isMultiplicative_sigma.map_mul_of_coprime hc] at bal
  have wp:=IsMultiplicative.map_prod z w_mult univ pair
  have sp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=1)) univ pair
  have tp:=IsMultiplicative.map_prod z (isMultiplicative_sigma (k:=0)) univ pair
  change W (total p e)=_ at wp
  change σ 1 (total p e)=_ at sp
  change σ 0 (total p e)=_ at tp
  simp only [z,sigma_zero_apply_prime_pow (pr _)] at tp
  let mass : ℚ:=∏ i,(((e i:ℕ):ℚ)+1)*(p i:ℚ)^e i
  have tax : mass = (total p e:ℚ)*(σ 0 (total p e):ℚ) := by
    rw [tp,total];push_cast;dsimp [mass];rw [prod_mul_distrib];ring
  have positive : 0 < mass := by
    apply prod_pos
    intro i _
    have := (pr i).pos
    positivity
  have wprod : (∏ i,X (p i) (some (e i)))*mass=(W (total p e):ℚ) := by
    rw [wp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>x_factor (pr i) (e i))
  have sprod : (∏ i,Y (p i) (some (e i)))*mass=(σ 1 (total p e):ℚ) := by
    rw [sp,←prod_mul_distrib];push_cast
    exact prod_congr rfl (fun i _=>y_factor (pr i) (e i))
  have D : 0<h*σ 0 h := Nat.mul_pos hh (sigma_pos 0 h hh.ne')
  have rat:=congrArg ((↑):ℕ→ℚ) bal
  push_cast at rat
  apply mul_right_cancel₀ (b:=mass) positive.ne'
  rw [add_mul,mul_assoc,mul_assoc,wprod,sprod,tax]
  field_simp [show ((h*σ 0 h:ℕ):ℚ)≠0 by exact_mod_cast D.ne']
  push_cast
  linear_combination rat


end OMA.CofactorCrossOriginal245212

end

section

/- An explicit whole-prime-power bound in the nonresonant case.
Replace large bases by 1 and small bases with large exponents by their
Euler limits. The explicitly separated subproduct cannot approximate a
solution this closely. -/
namespace OMA.CofactorEffectiveAtom245212
open Finset Nat OMA.Smooth245212 OMA.CofactorEulerSeparation245212

theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (x z : ι→ℚ)
    {w : ℚ} (wp : 0≤w) (bounds : ∀i∈s,0≤x i ∧ x i≤2 ∧ 0≤z i ∧ z i≤2 ∧ |x i-z i|≤w) :
    |(∏i∈s,x i)-(∏i∈s,z i)| ≤ s.card*(2:ℚ)^s.card*w := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s fresh ih=>
    let X:=∏j∈s,x j
    let Z:=∏j∈s,z j
    have b:=bounds i (mem_insert_self ..)
    have bs (j) (hj:j∈s):=bounds j (mem_insert_of_mem hj)
    have z0 : 0≤Z:=prod_nonneg (fun j hj=>(bs j hj).2.2.1)
    have z2 : Z≤(2:ℚ)^s.card := by
      simpa [Z] using prod_le_prod (fun j hj=>(bs j hj).2.2.1) (fun j hj=>(bs j hj).2.2.2.1)
    have old:=ih bs
    change |X-Z|≤_ at old
    rw [prod_insert fresh,prod_insert fresh,card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one,pow_succ]
    change |x i*X-z i*Z|≤_
    have tri:=abs_add_le (x i*(X-Z)) ((x i-z i)*Z)
    rw [show x i*(X-Z)+(x i-z i)*Z=x i*X-z i*Z by ring,abs_mul,abs_of_nonneg b.1,
      abs_mul,abs_of_nonneg z0] at tri
    have l:=mul_le_mul b.2.1 old (abs_nonneg _) (by decide : (0:ℚ)≤2)
    have r:=mul_le_mul b.2.2.2.2 z2 z0 wp
    nlinarith only [tri,l,r,mul_nonneg (pow_nonneg (by decide : (0:ℚ)≤2) s.card) wp]

private def factor (p : ℕ) : ℚ := (p:ℚ)/(p-1:ℕ)

private theorem local_factor {p e : ℕ} (hp : p.Prime) :
    1≤X p (some e) ∧ X p (some e)≤factor p ∧ factor p≤2 ∧
    factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
  have hi : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have den : (0:ℚ)<p-1 := by linarith
  have two : (2:ℚ)≤p := by exact_mod_cast hp.two_le
  have y0:=y_nonneg hp.one_lt (some e)
  have y1:=y_one hp.one_lt (some e)
  have diff : factor p-X p (some e)=Y p (some e)/((p:ℚ)-1) := by
    unfold factor X;push_cast [Nat.cast_sub hp.one_le];field_simp;ring
  refine ⟨le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr y1) den.le),?_,?_,diff⟩
  · linarith only [diff,div_nonneg y0 den.le]
  · unfold factor;push_cast [Nat.cast_sub hp.one_le];apply (div_le_iff₀ den).mpr;linarith

private theorem near {p e M : ℕ} (hp : p.Prime) (avoid : p≤M+1 → M<e) :
    |X p (some e)-(if p≤M+1 then factor p else 1)|≤2/((M:ℚ)+1) := by
  obtain ⟨low,hi,_,diff⟩:=local_factor (e:=e) hp
  have h2 : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
  have den : (0:ℚ)<p-1:=by linarith
  split
  next small=>
    rw [abs_of_nonpos (sub_nonpos.mpr hi),neg_sub,diff]
    have ye:=OMA.CapOrder245212.y_short hp e
    have big : (M:ℚ)+1≤e+1 := by exact_mod_cast (by have:=avoid small;omega : M+1≤e+1)
    have y0:=y_nonneg hp.one_lt (some e)
    calc
      Y p (some e)/((p:ℚ)-1) ≤ Y p (some e) := div_le_self y0 (by linarith)
      _ ≤ _ := (le_div_iff₀ (by positivity)).mpr ((mul_le_mul_of_nonneg_left big y0).trans ye.le)
  next large=>
    rw [abs_of_nonneg (sub_nonneg.mpr low)]
    unfold X
    have bound : (M:ℚ)+1≤p-1 := by
      have strong : (M:ℚ)+2≤p:=by exact_mod_cast (show M+2≤p by omega)
      linarith
    have y0:=y_nonneg hp.one_lt (some e)
    rw [add_sub_cancel_left]
    calc
      _ ≤ 1/((p:ℚ)-1) := div_le_div_of_nonneg_right (sub_le_self _ y0) den.le
      _ ≤ 1/((M:ℚ)+1) := one_div_le_one_div_of_le (by positivity) bound
      _ ≤ _ := by gcongr; norm_num

def threshold (A S K : ℕ) := budget A K*(2*A*K*2^K+2*S)

theorem alternative (A S H : ℕ) (s : Finset ℕ) (e : ℕ→ℕ) (pr : ∀p∈s,p.Prime)
    (apart : miss A H s)
    (bal : (A:ℚ)*(∏p∈s,X p (some (e p)))+S*(∏p∈s,Y p (some (e p)))=H) :
    let M:=threshold A S s.card
    (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M := by
  classical
  let K:=s.card
  let M:=threshold A S K
  change (∀p∈s,e p≤M) ∨ ∃p∈s,p≤M+1 ∧ e p≤M
  by_cases allSmall : ∀p∈s,e p≤M
  · exact Or.inl allSmall
  right
  by_contra no
  push Not at allSmall
  obtain ⟨j,hj,large⟩:=allSmall
  have avoid (p) (hp:p∈s) (low:p≤M+1) : M<e p := by
    by_contra! short
    exact no ⟨p,hp,low,short⟩
  let z (p : ℕ) : ℚ:=if p≤M+1 then factor p else 1
  let t:=s.filter (fun p=>p≤M+1)
  have sub : t⊆s:=filter_subset _ _
  have proxy : (∏p∈s,z p)=(num t:ℚ)/den t := by
    rw [show (∏p∈s,z p)=∏p∈t,factor p by simp [z,t,prod_filter]]
    unfold factor num den
    push_cast
    rw [prod_div_distrib]
  have sep:=rational_gap (A:=A) (H:=H) (K:=K) (s:=t) (card_le_card sub)
    (fun p hp=>(pr p (sub hp)).two_le) (fun u hu=>apart u (hu.trans sub))
  rw [←proxy] at sep
  have feat:=product_error s (fun p=>X p (some (e p))) z (w:=2/((M:ℚ)+1)) (by positivity)
    (fun p hp=>by
      have loc:=local_factor (e:=e p) (pr p hp)
      refine ⟨zero_le_one.trans loc.1,loc.2.1.trans loc.2.2.1,?_,?_,near (pr p hp) (avoid p hp)⟩
      · dsimp [z];split <;> first | exact (zero_le_one.trans loc.1).trans loc.2.1 | norm_num
      · dsimp [z];split <;> first | exact loc.2.2.1 | norm_num)
  let PX:=∏p∈s,X p (some (e p))
  let PY:=∏p∈s,Y p (some (e p))
  let Z:=∏p∈s,z p
  have y0 : 0≤PY:=prod_nonneg (fun p hp=>y_nonneg (pr p hp).one_lt _)
  have ylow : PY≤Y j (some (e j)) := by
    dsimp [PY];rw [←prod_erase_mul _ _ hj]
    exact mul_le_of_le_one_left (y_nonneg (pr j hj).one_lt _) (prod_le_one
      (fun p hp=>y_nonneg (pr p (mem_of_mem_erase hp)).one_lt _)
      (fun p hp=>y_one (pr p (mem_of_mem_erase hp)).one_lt _))
  have ycut := OMA.CapOrder245212.y_short (pr j hj) (e j)
  let L:ℚ:=M+1
  have lp : 0<L:=by dsimp [L];positivity
  have yl : PY*L≤2 := (mul_le_mul ylow (show L≤(e j:ℚ)+1 by dsimp [L];exact_mod_cast Nat.succ_le_succ large.le)
    lp.le (y_nonneg (pr j hj).one_lt _)).trans ycut.le
  change |PX-Z|≤K*(2:ℚ)^K*(2/L) at feat
  have xl : |PX-Z| * L≤K*2^K*2 := by
    apply (le_div_iff₀ lp).mp
    simpa [div_eq_mul_inv,mul_assoc] using feat
  change (A:ℚ)*PX+S*PY=H at bal
  change 1≤(budget A K:ℚ)*|(A:ℚ)*Z-H| at sep
  have tri:=abs_add_le ((A:ℚ)*(PX-Z)) ((S:ℚ)*PY)
  rw [show (A:ℚ)*(PX-Z)+S*PY=H-A*Z by linarith only [bal],abs_sub_comm (H:ℚ)] at tri
  simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg A : (0:ℚ)≤A),
    abs_of_nonneg (Nat.cast_nonneg S : (0:ℚ)≤S),abs_of_nonneg y0] at tri
  have distance : |(A:ℚ)*Z-H| * L≤2*A*K*2^K+2*S := by
    nlinarith only [mul_le_mul_of_nonneg_right tri lp.le,
      mul_le_mul_of_nonneg_left xl (Nat.cast_nonneg A : (0:ℚ)≤A),
      mul_le_mul_of_nonneg_left yl (Nat.cast_nonneg S : (0:ℚ)≤S)]
  have bad : L≤(budget A K:ℚ)*(2*A*K*2^K+2*S) := by
    nlinarith only [mul_le_mul_of_nonneg_right sep lp.le,
      mul_le_mul_of_nonneg_left distance (Nat.cast_nonneg (budget A K) : (0:ℚ)≤_)]
  change ((threshold A S K:ℕ):ℚ)+1≤_ at bad
  unfold threshold at bad
  push_cast at bad
  linarith

end OMA.CofactorEffectiveAtom245212

end

section

/- A missing interval among four ordered cutoffs makes the local tail
smaller than a nonzero integer's reciprocal denominator. -/
namespace OMA.ThreeMovingStep245212
open Nat Finset OMA.ThreeMovingLocal245212 OMA.ThreeMovingGap245212 OMA.ThreeMovingScalar245212
open OMA.CofactorEffectiveAtom245212 (product_error)

private theorem integer_gap (c : Family) (bits : Fin 3→Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

private theorem difference (c : Family) (b : Fin 3→Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀i,N ≤ (if b i then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤48*((f:ℚ)+g)/N := by
  have bp (i) := bounds (c.prime i) (c.positive i) c.mp (c.lengths i).1 (b i)
  have er (i) := error (c.prime i) (c.positive i) n0 (b i) (space i)
  have eps : (0:ℚ)≤2/N := by positivity
  have one : 2/(c.m:ℚ)≤2 := div_le_self (by decide) (by exact_mod_cast c.mp)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (bp i).1,(bp i).2.1,zero_le_one.trans (bp i).2.2.2.2.1,
      (bp i).2.2.2.2.2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactY c) (y' c b) eps
    (fun i _=>⟨(bp i).2.2.1,(bp i).2.2.2.1.trans one,(bp i).2.2.2.2.2.2.1,
      (bp i).2.2.2.2.2.2.2.trans one,(er i).2⟩)
  norm_num at x y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family) (f g l x : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (frac : f+g=(c.k+1)*l) (unit : ∀i,¬c.p i∣l)
    (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (powers : ∀i,x^budget≤(c.p i)^(c.e i))
    (actual : score f g (exactX c) (exactY c)≤(f+g:ℕ))
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^budget:ℕ):ℚ)) : False := by
  obtain ⟨j,band⟩:=empty_interval x (by omega) c.p
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3):Bool:=decide (c.p i≤Q)
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^budget:=cut_mono (by omega) (show j.val+1≤4 by omega)
  have space (i) : N ≤ (if b i then c.p i^c.e i else c.p i) := by
    dsimp [b];split
    · exact nb.trans (powers i)
    next h=>exact ((band i).resolve_left (by simpa using h)).le
  have ds : dust c b≤Q^9 := by
    have per i : den (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.lengths i).2.trans (cl.trans xQ)
      dsimp [den,b]
      split
      next h =>
        have small : c.p i≤Q:=by simpa using h
        exact (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring)
      next=>exact el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have nz:=nonzero c b f g l gp fg frac unit actual
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega

end OMA.ThreeMovingStep245212

end

section

namespace OMA.BoundedAtom245212
open Finset OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem normalized_dyadic {K : ℕ} (k : ℕ) (p e : Fin K → ℕ) (hp : ∀ i,Nat.Prime (p i))
    (op : ∀ i,Odd (p i)) (inj : p.Injective)
    (eq : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    X 2 (some k)*(∏ i,X (p i) (some (e i)))+
      Y 2 (some k)*(∏ i,Y (p i) (some (e i)))=2 := by
  let P : Fin (K+1) → ℕ := Fin.cons 2 p
  let E : Fin (K+1) → ℕ := Fin.cons k e
  have prime : ∀ i,Nat.Prime (P i) := Fin.cases Nat.prime_two hp
  have distinct : P.Injective := Fin.cons_injective_of_injective (by
    rintro ⟨i,hi⟩; have h := op i; rw [hi] at h; norm_num [Nat.odd_iff] at h) inj
  have all : total P E=2^k*total p e := by
    rw [total,Fin.prod_univ_succ]; rfl
  have norm := normalized_of_eq P prime distinct E (by rw [all]; exact eq)
  unfold normalized at norm
  rw [Fin.prod_univ_succ (fun i => X (P i) (some (E i))),
    Fin.prod_univ_succ (fun i => Y (P i) (some (E i)))] at norm
  exact norm


end OMA.BoundedAtom245212

end

section

/- For a fixed positive exponent vector there are finitely many choices of
prime bases at which a fixed positive combination of the two divisor products
can equal a given number. The products decrease when bases increase. -/
namespace OMA.FixedExponents245212
open Finset OMA.Smooth245212

theorem x_avg {p : ℕ} (hp : Nat.Prime p) (e : ℕ) :
    X p (some e)=(∑ j∈range (e+1),((e-j+1:ℕ):ℚ)*(p:ℚ)⁻¹^j)/((e:ℚ)+1) := by
  have xf := x_factor hp e
  rw [w_pow hp] at xf
  push_cast at xf
  have nz : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  apply (eq_div_iff (by positivity)).2
  apply mul_right_cancel₀ (pow_ne_zero e nz)
  rw [mul_assoc,xf,sum_mul]
  rw [←sum_range_reflect (fun j => (p:ℚ)^j*((j:ℚ)+1)) (e+1)]
  refine sum_congr rfl fun j hj => ?_
  have h : j≤e := by have := mem_range.mp hj; omega
  have h' : e+1-1-j=e-j := by omega
  rw [h',Nat.cast_add,Nat.cast_one]
  have add : j+(e-j)=e := by omega
  have cancel : (p:ℚ)⁻¹^j*(p:ℚ)^e=(p:ℚ)^(e-j) := by
    calc
      _ = (p:ℚ)⁻¹^j*((p:ℚ)^j*(p:ℚ)^(e-j)) := by rw [←pow_add,add]
      _ = _ := by rw [inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ nz),one_mul]
  rw [mul_assoc,cancel,mul_comm]

private theorem y_strict_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (pq : p<q) {e : ℕ} (ep : 0<e) : Y q (some e)<Y p (some e) := by
  rw [y_avg hq.one_lt,y_avg hp.one_lt]
  apply div_lt_div_of_pos_right _ (by positivity)
  apply sum_lt_sum
  · intro i _
    gcongr
    exact_mod_cast hp.pos
  · refine ⟨1,mem_range.mpr (by omega),?_⟩
    simp only [pow_one]
    apply inv_lt_inv₀ (by exact_mod_cast hq.pos) (by exact_mod_cast hp.pos) |>.mpr
    exact_mod_cast pq

private theorem x_le_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (pq : p≤q) (e : ℕ) : X q (some e)≤X p (some e) := by
  rw [x_avg hp,x_avg hq]
  gcongr
  exact_mod_cast hp.pos

theorem y_pos {p : ℕ} (hp : Nat.Prime p) (e : ℕ) : 0<Y p (some e) := by
  rw [y_avg hp.one_lt]
  apply div_pos _ (by positivity)
  exact sum_pos' (fun _ _ => by positivity) ⟨0,by simp,by simp⟩

theorem finite_bases {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (ep : ∀ i,0<e i) (a b t : ℚ) (ha : 0≤a) (hb : 0<b) :
    {p : ι → ℕ | (∀ i,Nat.Prime (p i)) ∧
      a*(∏ i,X (p i) (some (e i)))+b*(∏ i,Y (p i) (some (e i)))=t}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro p hp q hq diff pq
  obtain ⟨i,lt⟩ : ∃ i,p i<q i := by
    by_contra! h; exact diff (funext fun j => Nat.le_antisymm (pq j) (h j))
  have yp (j) := y_pos (hq.1 j) (e j)
  have xp := prod_le_prod (s:=univ) (fun j _ => x_nonneg (hq.1 j).one_lt (some (e j)))
    (fun j _ => x_le_prime (hp.1 j) (hq.1 j) (pq j) (e j))
  have ys (j) : Y (q j) (some (e j))≤Y (p j) (some (e j)) := by
    rcases (pq j).eq_or_lt with h|l
    · rw [h]
    · exact (y_strict_prime (hp.1 j) (hq.1 j) l (ep j)).le
  have strict := Finset.prod_lt_prod (s:=univ) (fun j _ => yp j) (fun j _ => ys j)
    ⟨i,mem_univ i,y_strict_prime (hp.1 i) (hq.1 i) lt (ep i)⟩
  linarith only [hp.2,hq.2,mul_le_mul_of_nonneg_left xp ha,mul_lt_mul_of_pos_left strict hb]

end OMA.FixedExponents245212

end

section

/- An upper bound on the power of two in terms of each odd prime divisor. -/
namespace OMA.DyadicLeast245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.FixedExponents245212 (x_avg)
open OMA.FixedExponents245212 (y_pos)

def term (p e : ℕ) : ℚ := (e:ℚ)/(((e:ℚ)+1)*p)

theorem x_two_terms {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    1+term p e ≤ X p (some e) := by
  rw [OMA.FixedExponents245212.x_avg hp]
  apply (le_div_iff₀ (by positivity)).mpr
  let z (i : ℕ) := ((e-i+1:ℕ):ℚ)*(p:ℚ)⁻¹^i
  have sub : range 2⊆range (e+1) := range_subset_range.mpr (by omega)
  have b := sum_le_sum_of_subset_of_nonneg (f:=z) sub (fun _ _ _ => by dsimp [z]; positivity)
  refine le_trans ?_ b
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one,z,Nat.sub_zero,
    Nat.cast_add,Nat.cast_one,Nat.cast_sub (show 1≤e by omega)]
  have pp : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  unfold term
  field_simp
  ring_nf
  exact le_rfl

private theorem sum_le_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p e : ι → ℕ) (hp : ∀ i,(p i).Prime) (he : ∀ i,0<e i) :
    1+∑ i∈s,term (p i) (e i)≤∏ i∈s,X (p i) (some (e i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi,prod_insert hi]
    have t0 (j) : 0≤term (p j) (e j) := by unfold term; positivity
    have s0 := sum_nonneg (s:=s) (fun j _ => t0 j)
    have b := mul_le_mul (x_two_terms (hp i) (he i)) ih (by linarith only [s0]) (x_nonneg (hp i).one_lt _)
    exact (show 1+(term (p i) (e i)+∑ j∈s,term (p j) (e j))≤_ by
      nlinarith only [mul_nonneg (t0 i) s0]).trans b

private theorem vector {K : ℕ} (k : ℕ) (p e : Fin K → ℕ) (hp : ∀ i,(p i).Prime)
    (he : ∀ i,0<e i) (eq : X 2 (some k)*(∏ i,X (p i) (some (e i)))+
      Y 2 (some k)*(∏ i,Y (p i) (some (e i)))=2) :
    (k:ℚ)*(∑ i,term (p i) (e i))<1 := by
  let c := X 2 (some k)
  let d := Y 2 (some k)
  let S := ∑ i,term (p i) (e i)
  have d0 : 0<d := OMA.FixedExponents245212.y_pos Nat.prime_two k
  have cd : c+d=2 := by dsimp [c,d,X]; norm_num; ring
  have kd : (k:ℚ)*d≤c := by
    have h := OMA.CapOrder245212.y_short prime_two k
    change d*((k:ℚ)+1)<2 at h
    linarith only [cd,h]
  have ys := prod_pos (s:=univ) (fun i _ => OMA.FixedExponents245212.y_pos (hp i) (e i))
  have s0 : 0≤S := sum_nonneg (fun i _ => by unfold term; positivity)
  have b := mul_le_mul_of_nonneg_left (sum_le_product univ p e hp he) (x_nonneg (by decide : 1<2) (some k))
  change c*(1+S)≤c*_ at b
  change c*_+d*_=2 at eq
  apply (mul_lt_mul_iff_right₀ d0).mp
  nlinarith only [eq,cd,b,mul_pos d0 ys,mul_le_mul_of_nonneg_right kd s0]

/-- The first two terms of each weighted prime factor already constrain
all odd prime reciprocals, independently of the divisor count. -/
theorem reciprocal_sum {k m : ℕ} (om : Odd m)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    (k:ℚ)*(∑ q∈m.primeFactors,term q (m.factorization q))<1 := by
  let F := m.primeFactors
  let p := F.orderEmbOfFin rfl
  let e (i : Fin F.card) := m.factorization (p i)
  have mem (i : Fin F.card) : p i∈m.primeFactors := orderEmbOfFin_mem F rfl i
  have hp (i) := prime_of_mem_primeFactors (mem i)
  have po (i) := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr om).of_dvd_right
    (dvd_of_mem_primeFactors (mem i)))
  have ep (i) := (hp i).factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors (mem i))
  have repr : total p e=m :=
    (Fintype.prod_equiv (F.orderIsoOfFin rfl).toEquiv _
      (fun j : F => j.val^(m.factorization j.val)) (fun _ => rfl)).trans
      (Nat.prod_primeFactors_coe_pow_factorization om.pos.ne').symm
  have sm := (Fintype.sum_equiv (F.orderIsoOfFin rfl).toEquiv (fun i => term (p i) (e i))
    (fun j : F => term j.val (m.factorization j.val)) (fun _ => rfl)).trans
    (Finset.sum_coe_sort F (fun q => term q (m.factorization q)))
  rw [←sm]
  exact vector k p e hp ep (OMA.BoundedAtom245212.normalized_dyadic k p e hp po p.injective
    (by rw [repr]; exact eq))

theorem exponent_lt_twice_prime {k m q : ℕ} (om : Odd m) (hq : q∈m.primeFactors)
    (eq : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : k<2*q := by
  have h := reciprocal_sum om eq
  have pr := prime_of_mem_primeFactors hq
  have ep := pr.factorization_pos_of_dvd om.pos.ne' (dvd_of_mem_primeFactors hq)
  have one := single_le_sum (f:=fun q => term q (m.factorization q)) (fun i _ => by unfold term; positivity) hq
  have ratio := (mul_le_mul_of_nonneg_left one (Nat.cast_nonneg k : (0:ℚ)≤k)).trans_lt h
  let e := m.factorization q
  have he : (1:ℚ)≤e := by exact_mod_cast ep
  have qp : (0:ℚ)<q := by exact_mod_cast pr.pos
  change (k:ℚ)*((e:ℚ)/((e+1)*q))<1 at ratio
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity),one_mul] at ratio
  by_contra! high
  have excess := mul_le_mul_of_nonneg_right (show (2:ℚ)*q≤k by exact_mod_cast high) (le_trans (by norm_num : (0:ℚ)≤1) he)
  nlinarith only [ratio,excess,mul_nonneg qp.le (sub_nonneg.mpr he)]


end OMA.DyadicLeast245212

end

section

/- Absolute bounds for the shortest of three moving odd prime exponents
if the longest is not too large. The dyadic exponent is unrestricted. -/
namespace OMA.ThreeMovingOriginal245212
open Nat Finset ArithmeticFunction OMA.ThreeMovingGap245212 OMA.ThreeMovingScalar245212
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)

def F (k : ℕ) := 1+k*2^(k+1)
def G (k : ℕ) := 2^(k+1)-1

theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩

theorem physical (c : Family) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]

private theorem small_case (c : Family) (hp : ∀i,3≤c.p i) (hk : ∀i,c.k<2*c.p i) (high : minimumCut≤c.m)
    (exact : score (F c.k) (G c.k) (exactX c) (exactY c)=(F c.k+G c.k:ℕ)) : False := by
  let x:=base c.k c.L
  have big : 128≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have comp : c.L≤c.k*c.m^2 := by have:=c.comparable;omega
  have powers i : x^degree≤c.p i^c.e i := scale (hp i) (hk i) high comp (c.lengths i).1
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.ThreeMovingLocal245212.bounds (c.prime i) (c.positive i) c.mp (c.lengths i).1 true
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤8 := calc
    _ ≤ ∏_i:Fin 3,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_cases ample : 8*(c.k+1)*x^budget≤G c.k
  · have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
      push_cast
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
    have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^budget:ℕ):ℚ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
      have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^budget:ℕ)≤1 := by
        apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
        have g0 : (8:ℚ)*(c.k+1)*(x^budget:ℕ)≤G c.k:=by exact_mod_cast ample
        push_cast at g0 ⊢
        nlinarith only [congrArg (·*(x:ℚ)^budget) id,g0,
          mul_le_mul_of_nonneg_right (show PX-1≤8 by linarith) (show 0≤((c.k:ℚ)+1)*x^budget by positivity)]
      exact (le_div_iff₀ (by exact_mod_cast pow_pos dx budget : (0:ℚ)<(x^budget:ℕ))).mpr h
    apply OMA.ThreeMovingStep245212.contradiction c c.k 1 1 x (by decide) (by simp) (by simp) _ big cf cl
      (fun i=>(Nat.pow_le_pow_right dx (show budget≤degree by decide)).trans (powers i)) below close
    intro i; exact Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt
  · let x':=x^(budget+4)
    have lift : x≤x':=Nat.le_self_pow (by omega : budget+4≠0) _
    have fcap : F c.k+G c.k≤x' := by
      have gcap : G c.k+1≤8*(c.k+1)*x^budget:=by omega
      have zid : 2^(c.k+1)=G c.k+1 := by dsimp [G];have:=Nat.two_pow_pos (c.k+1);omega
      rw [(identities c.k).2.1,zid]
      calc
        _ ≤ (c.k+1)*(8*(c.k+1)*x^budget) := Nat.mul_le_mul_left _ gcap
        _ = (c.k+1)*(8*((c.k+1)*x^budget)) := by ring
        _ ≤ x*(x*(x*x^budget)) := Nat.mul_le_mul cf (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ cf))
        _ = x^(budget+3) := by rw [pow_add];ring
        _ ≤ x' := Nat.pow_le_pow_right dx (by omega)
    apply OMA.ThreeMovingStep245212.contradiction c (F c.k) (G c.k) (2^(c.k+1)) x' r0
      (by have:=(identities c.k).2.2;omega) (identities c.k).2.1 _ (big.trans lift) fcap (cl.trans lift)
      (fun i=>by dsimp [x'];rw [←pow_mul];exact powers i) exact.le (by rw [exact,sub_self,abs_zero];positivity)
    intro i d
    have dv:=(c.prime i).dvd_of_dvd_pow d
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (hp i)) dv

theorem shortest {k m L : ℕ} (p e : Fin 3→ℕ) (hp : ∀i,(p i).Prime) (op : ∀i,Odd (p i)) (inj : p.Injective)
    (ep : ∀i,0<e i) (mp : 0 < m) (lengths : ∀i,m≤e i+1 ∧ e i+1≤L)
    (comparable : 4*max (max 1 k) L < max 1 k*m^2)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) : m < minimumCut := by
  by_contra! high
  let c : Family := ⟨p,e,max 1 k,m,L,hp,ep,by omega,mp,lengths,comparable⟩
  have p3 i : 3≤p i := by have:=(hp i).two_le;obtain ⟨j,ju⟩:=op i;omega
  have odd : Odd (total p e) := Nat.coprime_two_left.mp (Coprime.prod_right (fun i _=>(Nat.coprime_two_left.mpr (op i)).pow_right _))
  have inF i : p i∈(total p e).primeFactors := Nat.mem_primeFactors.mpr ⟨hp i,
    (dvd_pow_self _ (ep i).ne').trans (dvd_prod_of_mem (fun j=>p j^e j) (mem_univ i)),odd.pos.ne'⟩
  have dk i := OMA.DyadicLeast245212.exponent_lt_twice_prime odd (inF i) eqn
  have norm:=physical c k op inj eqn
  by_cases kp : 0<k
  · have ck : c.k=k:=max_eq_right kp
    apply small_case c p3 (fun i=>by rw [ck];exact dk i) high
    rw [ck];exact norm
  · have zero : k=0:=by omega
    subst k
    have ck : c.k=1:=rfl
    let x:=base 1 L
    have big : 128≤x := by dsimp [x,base];omega
    have cf : 2≤x:=by omega
    have cl : c.L≤x:=by change L≤128*(1+2)*(L+1);omega
    have limits i := scale (k:=1) (p:=p i) (e:=e i) (p3 i) (by have:=p3 i;omega) high
      (show L≤1*m^2 by norm_num at comparable ⊢;omega) (lengths i).1
    change score 1 1 (exactX c) (exactY c)=(1+1:ℕ) at norm
    exact OMA.ThreeMovingStep245212.contradiction c 1 1 1 x (by decide) (by rw [ck]) (by rw [ck])
      (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (hp i).one_lt) big cf cl
      (fun i=>(Nat.pow_le_pow_right (by omega : 0<x) (show budget≤degree by decide)).trans (limits i))
      norm.le (by rw [norm,sub_self,abs_zero];positivity)

end OMA.ThreeMovingOriginal245212

end

section

/- The denominator argument for truncating the Egyptian-fraction equation
for the odd part in A245212.  All sums here are over positive denominators. -/
namespace OMA.DivisorEnvelope245212
open Finset

private lemma div_cast {m d : ℕ} (hd : d ∈ m.divisors) :
    ((m/d : ℕ) : ℚ) = (m:ℚ)/d := by
  exact Nat.cast_div (Nat.mem_divisors.mp hd).1 (by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')

/-- Convert a weighted equation over divisor complements into a positive
Egyptian-fraction identity, omitting the known first denominator. -/
theorem egyptian {m : ℕ} (hm : 0 < m) (c : ℚ)
    (balance : ((m:ℚ)*m.divisors.card - ∑ d ∈ m.divisors, (d:ℚ)) =
      c*((∑ d ∈ m.divisors, (d:ℚ)*d.divisors.card)-(m:ℚ)*m.divisors.card)) :
    (m.divisors.card:ℚ)-1 =
      ∑ d ∈ m.divisors.erase 1, (c*((m/d).divisors.card:ℚ)+1)/d := by
  let w (d : ℕ) := (d:ℚ)*(c*d.divisors.card+1)
  have comp := Nat.sum_div_divisors m w
  have id' : ∑ d ∈ m.divisors, (c*((m/d).divisors.card:ℚ)+1)/d =
      (∑ d ∈ m.divisors, w d)/m := by
    rw [←comp, Finset.sum_div]
    refine sum_congr rfl fun d hd => ?_
    dsimp [w]
    rw [div_cast hd]
    field_simp
  have one := Nat.one_mem_divisors.mpr hm.ne'
  have erase := Finset.sum_erase_add _ (fun d : ℕ => (c*((m/d).divisors.card:ℚ)+1)/d) one
  simp only [Nat.div_one,Nat.cast_one,div_one] at erase
  dsimp [w] at id'
  simp_rw [mul_add,mul_one,mul_left_comm (_:ℚ) c] at id'
  rw [sum_add_distrib,←mul_sum] at id'
  have id'' := (eq_div_iff (by exact_mod_cast hm.ne' : (m:ℚ)≠0)).1 id'
  rw [←erase] at id''
  apply (mul_right_cancel₀ (by exact_mod_cast hm.ne' : (m:ℚ) ≠ 0))
  linear_combination balance - id''

/-- The common denominator itself, not its square, controls the strict gap
between an integer and a partial divisor-reciprocal sum. -/
theorem gap {b t : ℕ} (hb : 0<b) (s : Finset ℕ) (u : ℕ → ℕ)
    (den : ∀ d ∈ s, d∣b) (pos : ∀ d ∈ s, 0<d)
    (lt : (∑ d ∈ s, (u d : ℚ)/d) < t) :
    1/(b:ℚ) ≤ t-∑ d ∈ s, (u d : ℚ)/d := by
  let v := ∑ d ∈ s, u d*(b/d)
  have id' : ((∑ d ∈ s, (u d:ℚ)/d)*(b:ℚ)) = (v:ℚ) := by
    dsimp [v]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun d hd => ?_
    rw [Nat.cast_div (den d hd) (by exact_mod_cast (pos d hd).ne')]
    ring
  have bl : (0:ℚ)<b := by exact_mod_cast hb
  have h := mul_lt_mul_of_pos_right lt bl
  rw [id'] at h
  have hn : v < t*b := by exact_mod_cast h
  have step : (v:ℚ)+1 ≤ (t:ℚ)*b := by exact_mod_cast hn
  apply (div_le_iff₀ bl).2
  rw [sub_mul,id']
  linarith

/-- An integer Egyptian-fraction target and a common positive perturbation
give an explicit lower bound on the tails left by a divisor cutoff. -/
theorem truncated {s : Finset ℕ} (nonempty : s.Nonempty) {u : ℕ → ℕ}
    {t a b P y : ℕ} (hb : 0<b) (hp : 0<P)
    (count : s.card≤t) (hpos : ∀ d∈s, 0<d)
    (wu : ∀ d∈s, 0<u d ∧ u d≤t) (tail : ∀ d∈s, ¬d∣b → P≤d)
    {δ : ℚ} (hδ : 0<δ)
    (target : (y:ℚ) = ∑ d∈s, (((a:ℚ)+δ)*u d+1)/d) :
    1/(b:ℚ) ≤ t*(δ*t+(((a:ℚ)+δ)*t+1)/P) := by
  classical
  let F := s.filter (· ∣ b)
  let v (d : ℕ) : ℚ := if d∣b then ((a*u d+1:ℕ):ℚ)/d else 0
  let w (d : ℕ) : ℚ := (((a:ℚ)+δ)*u d+1)/d
  have cut : ∑ d∈s, v d = ∑ d∈F, ((a*u d+1:ℕ):ℚ)/d := by
    simp [v,F,sum_filter]
  have diff (d : ℕ) (hd : d∈s) :
      0<w d-v d ∧ w d-v d≤δ*t+(((a:ℚ)+δ)*t+1)/P := by
    have dp : (0:ℚ)<d := by exact_mod_cast hpos d hd
    have one : (1:ℚ)≤d := by exact_mod_cast hpos d hd
    have up : (0:ℚ)<u d := by exact_mod_cast (wu d hd).1
    have ut : (u d:ℚ)≤t := by exact_mod_cast (wu d hd).2
    have pp : (0:ℚ)<P := by exact_mod_cast hp
    dsimp [w,v]
    by_cases dd : d∣b
    · rw [if_pos dd]
      push_cast
      rw [←sub_div,show ((a:ℚ)+δ)*u d+1-(a*u d+1)=δ*u d by ring]
      constructor
      · positivity
      · calc
          _ ≤ δ*u d := div_le_self (by positivity) one
          _ ≤ δ*t := by gcongr
          _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg dd,sub_zero]
      constructor
      · positivity
      · have pd : (P:ℚ)≤d := by exact_mod_cast tail d hd dd
        calc
          _ ≤ (((a:ℚ)+δ)*t+1)/P := by gcongr
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have strict : (∑ d∈F, ((a*u d+1:ℕ):ℚ)/d) < y := by
    rw [←cut,target]
    exact sum_lt_sum_of_nonempty nonempty (fun d hd => sub_pos.mp (diff d hd).1)
  have lower := gap hb F (fun d => a*u d+1)
    (fun d hd => (mem_filter.mp hd).2)
    (fun d hd => hpos d (mem_filter.mp hd).1) strict
  rw [←cut,target,←sum_sub_distrib] at lower
  calc
    _ ≤ ∑ d∈s, (w d-v d) := lower
    _ ≤ ∑ _d∈s, (δ*t+(((a:ℚ)+δ)*t+1)/P) := sum_le_sum fun d hd => (diff d hd).2
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr

/-- Finite bootstrap: if at each stage either an integer is already
bounded or the next prime base is bounded, the cumulative height exponent
is the product of the local divisor counts. -/
theorem bootstrap {r B H : ℕ} {p e : ℕ → ℕ} (hH : 1≤H)
    (step : ∀ j<r,
      B ≤ H*(∏ i ∈ range j, (p i)^(e i)) ∨
      p j ≤ H*(∏ i ∈ range j, (p i)^(e i)))
    (last : B ≤ H*(∏ i ∈ range r, (p i)^(e i))) :
    B ≤ H^(∏ i ∈ range r, (e i+1)) := by
  let m (j : ℕ) := ∏ i ∈ range j, (p i)^(e i)
  let t (j : ℕ) := ∏ i ∈ range j, (e i+1)
  have grow (j : ℕ) : H^(t j) ≤ H^(t (j+1)) := by
    apply Nat.pow_le_pow_right hH
    simp only [t,prod_range_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
  have aux (j : ℕ) (hj : j≤r) : B≤H^(t j) ∨ H*m j ≤ H^(t j) := by
    induction j with
    | zero => exact Or.inr (by simp [m,t])
    | succ j ih =>
      rcases ih (by omega) with done|bound
      · exact Or.inl (done.trans (grow j))
      rcases step j (by omega) with done|next
      · exact Or.inl ((done.trans bound).trans (grow j))
      right
      have hp : p j ≤ H*m j := next
      calc
        H*m (j+1) = H*m j*(p j)^(e j) := by simp [m,prod_range_succ,mul_assoc]
        _ ≤ (H*m j)^(e j+1) := by rw [pow_succ']; gcongr
        _ ≤ (H^(t j))^(e j+1) := Nat.pow_le_pow_left bound _
        _ = H^(t (j+1)) := by rw [←pow_mul]; simp [t,prod_range_succ]
  rcases aux r le_rfl with h|h
  · exact h
  · exact last.trans h

end OMA.DivisorEnvelope245212

end

section

/- Effective height bounds from the original A245212 equality. -/
namespace OMA.DivisorHeight245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.DivisorEnvelope245212
open scoped ArithmeticFunction.sigma

theorem dyadic_moments (a : ℕ) :
    W (2^a) = a*2^(a+1)+1 ∧ σ 1 (2^a)+1 = 2^(a+1) := by
  rw [w_pow Nat.prime_two,sigma_one_apply_prime_pow Nat.prime_two]
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [sum_range_succ (fun j => 2^j*(j+1)) (a+1),
      sum_range_succ (fun j => 2^j) (a+1),ih.1,pow_succ (2:ℕ) (a+1)]
    constructor <;> nlinarith only [ih.2]

/-- At equality the odd part gives an integer target and a common rational
perturbation of the coefficients, including for an odd input (a=0). -/
theorem identity {a m : ℕ} (odd : Odd m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    (m.divisors.card:ℚ)-1 = ∑ d∈m.divisors.erase 1,
      (((a:ℚ)+((a:ℚ)+1)/(2^(a+1)-1))*(m/d).divisors.card+1)/d := by
  apply egyptian odd.pos
  have cp := (Nat.coprime_two_left.mpr odd).pow_left a
  have natBal := OMA.Abundance245212.balance (mul_ne_zero (pow_ne_zero _ (by decide)) odd.pos.ne') eqn
  rw [w_mult.map_mul_of_coprime cp,isMultiplicative_sigma.map_mul_of_coprime cp,
    isMultiplicative_sigma.map_mul_of_coprime cp,sigma_zero_apply_prime_pow Nat.prime_two,
    (dyadic_moments a).1] at natBal
  have bal := congrArg (Nat.cast : ℕ → ℚ) natBal
  have geom := congrArg (Nat.cast : ℕ → ℚ) (dyadic_moments a).2
  push_cast at bal geom
  rw [sigma_zero_apply,w_apply,sigma_one_apply (n:=m)] at bal
  push_cast at bal
  have dp : 1 < (2:ℚ)^(a+1) := one_lt_pow₀ (by norm_num) (by omega)
  field_simp [sub_ne_zero.mpr dp.ne']
  rw [pow_succ (2:ℚ) a] at bal geom ⊢
  linear_combination -bal + geom * (∑ d ∈ m.divisors, (d:ℚ))

private theorem tail_cut {m d : ℕ} (hd : d∈m.divisors) {s : Finset ℕ}
    (support : d.primeFactors ⊆ s) :
    d ∣ ∏ p∈s, p^m.factorization p := by
  have dz := (Nat.pos_of_mem_divisors hd).ne'
  obtain ⟨div,mz⟩ := Nat.mem_divisors.mp hd
  trans ∏ p∈d.primeFactors, p^m.factorization p
  · nth_rw 1 [Nat.prod_primeFactors_pow_factorization dz]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun p _ =>
      pow_dvd_pow _ ((Nat.factorization_le_iff_dvd dz mz).mpr div p)
  · exact Finset.prod_dvd_prod_of_subset _ _ _ support

private def core (m : ℕ) (s : Finset ℕ) := ∏ p∈s,p^m.factorization p

private theorem prefix_pos {m : ℕ} {s : Finset ℕ} (ss : s ⊆ m.primeFactors) :
    0 < core m s :=
  Finset.prod_pos fun _ h => Nat.pow_pos (Nat.prime_of_mem_primeFactors (ss h)).pos

/-- Advance through the prime factors in order, with all exponents taken
at once. The height exponent spent on p^e is exactly e+1. -/
private theorem prime_bootstrap {m B H : ℕ} (mp : 0 < m)
    (step : ∀ s ⊆ m.primeFactors, ∀ P : ℕ, 0<P →
      (∀ p∈m.primeFactors \ s,P≤p) → B≤H*core m s ∨ P≤H*core m s) :
    B≤H^m.divisors.card := by
  classical
  let M := m.primeFactors
  let t (r : Finset ℕ) := ∏ p∈r,(m.factorization p+1)
  have aux (r : Finset ℕ) (sub : r⊆M) :
      B≤(H*core m (M\r))^(t r) := by
    induction r using Finset.strongInductionOn with | _ r ih =>
    let s := M\r
    have ss : s ⊆ M := sdiff_subset
    have rem : M\s=r := by ext x; simp [s]; grind
    have hr : 0<t r := prod_pos fun _ _ => Nat.succ_pos _
    by_cases done : B≤H*core m s
    · exact done.trans (Nat.le_self_pow hr.ne' _)
    by_cases ne : r.Nonempty
    · let p := r.min' ne
      have pr : p ∈ r := min'_mem _ _
      have ps : p ∉ s := fun h => (mem_sdiff.mp h).2 pr
      have subset := (erase_subset p r).trans sub
      have key := (step s ss p (Nat.prime_of_mem_primeFactors (sub pr)).pos
        (by rw [rem]; exact fun q hq => min'_le _ _ hq)).resolve_left done
      have insert_eq : M\(r.erase p)=insert p s := by
        ext x; simp [s]; grind
      have up : H*core m (M\(r.erase p)) ≤ (H*core m s)^(m.factorization p+1) := by
        rw [insert_eq,core,prod_insert ps,pow_succ']
        change H*(p^m.factorization p*core m s) ≤ _
        rw [show H*(p^m.factorization p*core m s)=(H*core m s)*p^m.factorization p by ring]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left key _)
      have rest := ih (r.erase p) (erase_ssubset pr) subset
      apply rest.trans ((Nat.pow_le_pow_left up _).trans_eq ?_)
      rw [←pow_mul]
      congr 1
      exact mul_prod_erase r (fun q => m.factorization q+1) pr
    · have z := step s ss (H*core m s+1) (by omega) (by
        change ∀ p∈M\s,_
        simp [rem,not_nonempty_iff_eq_empty.mp ne])
      omega
  simpa [M,t,core,Nat.card_divisors mp.ne'] using aux M (Subset.rfl)

private theorem tail_prime {m P : ℕ} {s : Finset ℕ} (hP : ∀ p∈m.primeFactors\s,P≤p)
    {d : ℕ} (hd : d∈m.divisors) (nd : ¬d∣core m s) : P≤d := by
  by_contra! small
  apply nd (tail_cut hd ?_)
  intro p h
  by_contra out
  have hm := Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hd).2 h
  exact small.not_ge ((hP p (mem_sdiff.mpr ⟨hm,out⟩)).trans (Nat.le_of_mem_primeFactors h))

private theorem counts {m d : ℕ} (hd : d ∈ m.divisors) :
    0 < (m/d).divisors.card ∧ (m/d).divisors.card ≤ m.divisors.card := by
  obtain ⟨dv,mz⟩ := Nat.mem_divisors.mp hd
  have prod := Nat.div_mul_cancel dv
  have nz : m/d≠0 := by intro h; simp [h] at prod; exact mz prod.symm
  exact ⟨card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr nz⟩,
    card_le_card (Nat.divisors_subset_of_dvd mz (Nat.div_dvd_of_dvd dv))⟩

private theorem dyadic_step {a t b P : ℕ} (ht : 0<t) (hb : 0<b)
    {δ : ℚ} (δ1 : δ≤1) (δ2 : δ≤((a:ℚ)+1)/2^a)
    (lower : 1/(b:ℚ) ≤ t*(δ*t+(((a:ℚ)+δ)*t+1)/P)) :
    2^a≤4*(a+2)*t^2*b ∨ P≤4*(a+2)*t^2*b := by
  by_contra! both
  let L : ℚ := 4*(a+2:ℚ)*t^2*b
  have bp : (0:ℚ)<b := by exact_mod_cast hb
  have tp : (0:ℚ)<t := by exact_mod_cast ht
  have t1 : (1:ℚ)≤t := by exact_mod_cast ht
  have lp : 0<L := by dsimp [L]; positivity
  have ll : L≤(2:ℚ)^a := by dsimp [L]; exact_mod_cast both.1.le
  have pl : L≤(P:ℚ) := by dsimp [L]; exact_mod_cast both.2.le
  have δ3 : δ≤((a:ℚ)+1)/L := δ2.trans (by gcongr)
  have z : t*(δ*t+(((a:ℚ)+δ)*t+1)/P) ≤
      t*((((a:ℚ)+1)/L)*t+(((a:ℚ)+1)*t+1)/L) := by gcongr
  have strict : (t:ℚ)*((((a:ℚ)+1)/L)*t+(((a:ℚ)+1)*t+1)/L) < 1/b := by
    field_simp [lp.ne',bp.ne']
    dsimp [L]
    have posat : 0≤(a:ℚ)*t := by positivity
    nlinarith only [mul_pos tp bp, mul_nonneg (sub_nonneg.mpr t1) (mul_pos tp bp).le,
      mul_nonneg posat (mul_pos tp bp).le]
  exact (lower.trans z).not_gt strict

/-- At a solution the power of two has an upper bound whose exponent is
only the number of odd divisors, independent of the prime bases. -/
theorem dyadic_height {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    2^a≤(4*(a+2)*m.divisors.card^2)^m.divisors.card := by
  let t := m.divisors.card
  have tp : 0<t := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  apply prime_bootstrap odd.pos
  intro s ss P pp hP
  let δ : ℚ := ((a:ℚ)+1)/(2^(a+1)-1)
  have b := prefix_pos ss
  have power : (1:ℚ)≤2^a := one_le_pow₀ (by norm_num)
  have z : (0:ℚ)<2^(a+1)-1 := by rw [pow_succ]; linarith
  have δ1 : δ≤1 := by
    apply (div_le_iff₀ z).mpr
    have grow := (a+1).lt_two_pow_self
    have aux : a+1+1≤2^(a+1) := grow
    have q : (a:ℚ)+1+1≤2^(a+1) := by exact_mod_cast aux
    linarith
  have δ2 : δ≤((a:ℚ)+1)/2^a := by
    dsimp [δ]; gcongr
    rw [pow_succ]; linarith
  have en : (m.divisors.erase 1).Nonempty := ⟨m,mem_erase.mpr ⟨by omega,Nat.mem_divisors_self _ odd.pos.ne'⟩⟩
  have iden := identity odd eqn
  have target : ((t-1:ℕ):ℚ) = ∑ d∈m.divisors.erase 1,
      (((a:ℚ)+δ)*(m/d).divisors.card+1)/d := by
    rw [Nat.cast_sub (by omega : 1≤t)]
    exact iden
  exact dyadic_step tp b δ1 δ2 (truncated en b pp (card_le_card (erase_subset _ _))
    (fun _ h => Nat.pos_of_mem_divisors (mem_of_mem_erase h))
    (fun _ h => counts (mem_of_mem_erase h)) (fun _ h => tail_prime hP (mem_of_mem_erase h))
    (div_pos (by positivity) z) target)

/-- A plain integer bound on the dyadic exponent; no root finding or
exponential search is required to turn the implicit bound into a cutoff. -/
theorem exponent_cutoff {a t : ℕ} (ht : 0<t) (h : 2^a≤(4*(a+2)*t^2)^t) :
    a<t*(2*Nat.log 2 (8*t^3)+2) := by
  let x := a/t
  have lo : x*t≤a := Nat.div_mul_le_self _ _
  have hi : a<(x+1)*t := by
    have rem := Nat.mod_lt a ht
    have eqn := Nat.mod_add_div a t
    dsimp [x]; nlinarith only [rem,eqn]
  have top : a+2≤(x+2)*t := by nlinarith only [hi,ht]
  have base : 2^x≤4*(a+2)*t^2 := by
    apply (Nat.pow_le_pow_iff_left ht.ne').mp
    rw [←pow_mul]; exact (Nat.pow_le_pow_right (by decide) lo).trans h
  have scale : 2*2^x≤8*(x+2)*t^3 := by
    have b := Nat.mul_le_mul_right (4*t^2) top
    nlinarith only [base,b]
  have half : x+2 ≤ 2*2^(x-x/2) := by
    have f := (x-x/2).lt_two_pow_self
    omega
  have hhalf := Nat.mul_le_mul_left (2^(x/2)) half
  rw [show 2^(x/2)*(2*2^(x-x/2))=2*2^x by
    rw [←Nat.mul_assoc,Nat.mul_comm (2^(x/2)) 2,Nat.mul_assoc,←pow_add]
    rw [Nat.add_sub_of_le (Nat.div_le_self x 2)]] at hhalf
  have cap : 2^(x/2)≤8*t^3 := by
    apply (mul_le_mul_iff_left₀ (Nat.succ_pos (x+1))).mp
    nlinarith only [hhalf,scale]
  have logBound := Nat.le_log_of_pow_le (by decide : 1<2) cap
  apply hi.trans_le
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left t (by omega)

/-- For unperturbed integer weights the strict gap is either absent, or
it forces the next omitted denominator to be small. -/
private theorem exact_cut {s : Finset ℕ} {w : ℕ → ℕ} {y b P t M : ℕ}
    (bp : 0<b) (pp : 0<P) (card : s.card≤t) (ds : ∀ d∈s,0<d)
    (ws : ∀ d∈s,0<w d ∧ w d≤M) (tail : ∀ d∈s,¬d∣b → P≤d)
    (idn : (y:ℚ)=∑ d∈s,(w d:ℚ)/d) :
    (∀ d∈s,d∣b) ∨ P≤b*t*M := by
  classical
  by_cases all : ∀ d∈s,d∣b
  · exact Or.inl all
  right
  push Not at all
  obtain ⟨d,hd,nd⟩ := all
  let f := s.filter (·∣b)
  let r := s\f
  have inside := filter_subset (fun d => d∣b) s
  have rest : ∀ i∈r,i∈s ∧ ¬i∣b := by
    intro i h
    obtain ⟨hs,hf⟩ := mem_sdiff.mp h
    exact ⟨hs,fun dv => hf (mem_filter.mpr ⟨hs,dv⟩)⟩
  have positive : 0<∑ i∈r,(w i:ℚ)/i := by
    apply sum_pos' (fun _ _ => by positivity)
    exact ⟨d,mem_sdiff.mpr ⟨hd,fun h => nd (mem_filter.mp h).2⟩,
      div_pos (by exact_mod_cast (ws d hd).1) (by exact_mod_cast ds d hd)⟩
  have split := sum_sdiff inside (f:=fun i => (w i:ℚ)/i)
  change (∑ i∈r,(w i:ℚ)/i)+(∑ i∈f,(w i:ℚ)/i)=_ at split
  rw [←idn] at split
  have lower := gap bp f w (fun i h => (mem_filter.mp h).2)
    (fun i h => ds i (mem_filter.mp h).1) (show (∑ i∈f,(w i:ℚ)/i)<y by linarith)
  have upper : (∑ i∈r,(w i:ℚ)/i) ≤ t*((M:ℚ)/P) := by
    calc
      _ ≤ ∑ _i∈r,(M:ℚ)/P := by
        apply sum_le_sum; intro i hi
        obtain ⟨si,ni⟩ := rest i hi
        have pe : (P:ℚ) ≤ i := by exact_mod_cast tail i si ni
        have wp : (w i:ℚ)≤M := by exact_mod_cast (ws i si).2
        gcongr
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul]
        gcongr
        exact (card_le_card (sdiff_subset : r⊆s)).trans card
  have le : 1/(b:ℚ) ≤ t*((M:ℚ)/P) := by linarith
  have bq : 0<(b:ℚ) := by exact_mod_cast bp
  have pq : 0<(P:ℚ) := by exact_mod_cast pp
  field_simp at le
  exact_mod_cast (show (P:ℚ) ≤ b*t*M by linarith only [le])

/-- Explicit upper bound on the odd part itself. -/
theorem odd_height {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    m≤((2^(a+1)-1)*(a+2)*m.divisors.card^2)^(m.divisors.card-1) := by
  let t := m.divisors.card
  let z : ℕ := 2^(a+1)-1
  let K := z*(a+2)*t^2
  let u (d : ℕ) := (m/d).divisors.card
  let w (d : ℕ) := (a*z+(a+1))*u d+z
  have tpos : 0<t := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  have grow := (a+1).lt_two_pow_self
  have az : a+1≤z := by dsimp [z]; omega
  have zp : 0<z := by omega
  have kp : 0<K := by dsimp only [K]; positivity
  have castz : (z:ℚ)=2^(a+1)-1 := by
    dsimp [z]; rw [Nat.cast_sub (by omega : 1≤(2:ℕ)^(a+1))]; push_cast; rfl
  have zq : (z:ℚ)≠0 := by exact_mod_cast zp.ne'
  have target : (((t-1)*z:ℕ):ℚ)=∑ d∈m.divisors.erase 1,(w d:ℚ)/d := by
    have idn := identity odd eqn
    rw [←castz] at idn
    push_cast [Nat.cast_sub (by omega : 1≤t)]
    rw [show (t:ℚ)-1=(m.divisors.card:ℚ)-1 from rfl,idn,sum_mul]
    apply sum_congr rfl
    intro d hd
    dsimp only [w,u]
    push_cast
    field_simp
  have cap : K*m≤K^t := by
    apply prime_bootstrap odd.pos
    intro s ss P pp hP
    have ww (d : ℕ) (h : d∈m.divisors.erase 1) : 0<w d ∧ w d≤z*(a+2)*t := by
      have c := (counts (mem_of_mem_erase h)).2
      change u d≤t at c
      constructor
      · dsimp [w]; positivity
      · calc
          w d ≤ (a*z+z)*t+z := by dsimp [w]; gcongr
          _ ≤ z*(a+2)*t := by
            have bz := Nat.mul_le_mul_left z (show 1≤t from tpos)
            nlinarith only [bz]
    rcases exact_cut (prefix_pos ss) pp (card_le_card (erase_subset _ _ ) : (m.divisors.erase 1).card≤t)
      (fun d h => Nat.pos_of_mem_divisors (mem_of_mem_erase h)) ww
      (fun d h => tail_prime hP (mem_of_mem_erase h)) target with all|bound
    · left; apply Nat.mul_le_mul_left
      exact Nat.le_of_dvd (prefix_pos ss) (all m (mem_erase.mpr ⟨by omega,Nat.mem_divisors_self _ odd.pos.ne'⟩))
    · right; apply bound.trans_eq; dsimp [K]; ring
  have eqt : t=(t-1)+1 := by omega
  rw [eqt] at cap
  rw [pow_succ'] at cap
  exact (mul_le_mul_iff_right₀ kp).mp cap

/-- Every fixed odd divisor count comes with a finite rectangular search
space given solely by that count. This does not bound t itself. -/
def exponentLimit (t : ℕ) := t*(2*Nat.log 2 (8*t^3)+2)
def coreLimit (t : ℕ) :=
  ((2^(exponentLimit t+1)-1)*(exponentLimit t+2)*t^2)^(t-1)

theorem effective_box {a m : ℕ} (odd : Odd m) (hm : 1 < m)
    (eqn : OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ)) :
    a<exponentLimit m.divisors.card ∧ m≤coreLimit m.divisors.card := by
  have ht : 0 < m.divisors.card := card_pos.mpr ⟨m,Nat.mem_divisors_self _ odd.pos.ne'⟩
  have ka := exponent_cutoff ht (dyadic_height odd hm eqn)
  refine ⟨ka,(odd_height odd hm eqn).trans ?_⟩
  dsimp only [coreLimit]
  gcongr <;> first | exact ka.le | decide

end OMA.DivisorHeight245212

end

section

namespace OMA.DyadicPower245212
open Nat Finset OMA.Smooth245212
theorem dyadic_odd (k : ℕ) : Odd (W (2^k)) := by
  rw [w_pow Nat.prime_two,Nat.odd_iff,sum_range_succ']
  have h : 2∣∑ i∈range k, 2^(i+1)*(i+1+1) :=
    Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
  simp only [pow_zero,zero_add,one_mul]
  omega


end OMA.DyadicPower245212

end

section

/- Effective recovery of the only possible last prime from its cofactor
and exponent, by bounding the lower digits in the divisor identity. -/
namespace OMA.LastDigit245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

def digitSum (p A S e : ℕ) := ∑ j∈range e,p^j*(A*(j+1)+S)
def denom (A S T d : ℕ) := 2*T*(d+1)-(A*(d+1)+S)

private theorem digit_pos {p A S d : ℕ} (hs : 0<S) (hd : 0<d) :
    0<digitSum p A S d := by
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨0,mem_range.mpr hd,by simpa using (show 0<A+S by omega)⟩

theorem geom (p e : ℕ) (hp : 1≤p) :
    (∑ j∈range e,p^j)*(p-1)+1=p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ,add_mul,pow_succ]
    have v := congrArg (fun x : ℕ => p^e*x) (Nat.sub_add_cancel hp)
    simp only [Nat.mul_add,Nat.mul_one] at v
    nlinarith only [ih,v]

theorem digits {p A S T d : ℕ} (hp : 1<p) (hs : 0<S) (hd : 0<d)
    (eq : digitSum p A S (d+1)=p^d*(2*T*(d+1))) :
    0<denom A S T d ∧ denom A S T d*(p-1)<A*d+S ∧ A*d+S≤denom A S T d*p ∧
      (1<d → A*d+S<denom A S T d*p) := by
  have dp := digit_pos (p:=p) (A:=A) hs hd
  have h := eq
  rw [digitSum,sum_range_succ,←digitSum] at h
  have co : A*(d+1)+S<2*T*(d+1) := by
    by_contra! v
    have := Nat.mul_le_mul_left (p^d) v
    omega
  have cut := Nat.sub_add_cancel co.le
  change denom A S T d+_= _ at cut
  have rest : digitSum p A S d=p^d*denom A S T d := by
    rw [←cut] at h
    rw [Nat.mul_add (p^d) (denom A S T d)] at h
    exact Nat.add_right_cancel h
  have ppos : 0<p^d := by positivity
  have up : digitSum p A S d ≤ (∑ j∈range d,p^j)*(A*d+S) := by
    rw [sum_mul]
    exact sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left A (mem_range.mp hj)) S))
  have sm := Nat.mul_le_mul_right (p-1) up
  have strict : denom A S T d*(p-1)<A*d+S := by
    apply Nat.lt_of_mul_lt_mul_left (a:=p^d)
    calc
      p^d*(denom A S T d*(p-1)) = digitSum p A S d*(p-1) := by rw [rest,mul_assoc]
      _ ≤ ((∑ j∈range d,p^j)*(p-1))*(A*d+S) := by simpa only [mul_right_comm] using sm
      _ < p^d*(A*d+S) := Nat.mul_lt_mul_of_pos_right (by have := geom p d hp.le; omega) (by omega)
  refine ⟨Nat.sub_pos_of_lt co,strict,?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [digitSum,sum_range_succ,←digitSum,pow_succ,mul_assoc] at rest
  have v : (A*(k+1)+S)*p^k ≤ (denom A S T (k+1)*p)*p^k := by
    nlinarith only [rest, Nat.zero_le (digitSum p A S k)]
  have pk : 0<p^k := by positivity
  exact ⟨(le_of_mul_le_mul_right v pk), fun hk =>
    (lt_of_mul_lt_mul_right (by nlinarith only [rest, digit_pos (p:=p) (A:=A) hs (by omega : 0<k)] :
      (A*(k+1)+S)*p^k < (denom A S T (k+1)*p)*p^k) (Nat.zero_le _))⟩

theorem balance_digits {p m d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p) (hd : 0<d)
    (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) :
    let A := W m; let S := σ 1 m; let T := m*(σ 0 m);
    0<denom A S T d ∧ denom A S T d*(p-1)<A*d+S ∧ A*d+S≤denom A S T d*p ∧
      (1<d → A*d+S<denom A S T d*p) := by
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  have c := cop.pow_right d
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    isMultiplicative_sigma.map_mul_of_coprime c,w_pow hp,sigma_one_apply_prime_pow hp,
    sigma_zero_apply_prime_pow hp] at b
  have spos : 0<σ 1 m := by
    rw [sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  apply digits hp.one_lt spos hd
  unfold digitSum
  simp_rw [show ∀ j:ℕ,p^j*(W m*(j+1)+σ 1 m)=W m*(p^j*(j+1))+σ 1 m*p^j by intro j; ring]
  rw [sum_add_distrib,←mul_sum,←mul_sum]
  simpa only [mul_comm,mul_left_comm,mul_assoc] using b

end OMA.LastDigit245212

end

section

/- A uniform effective restriction on every coprime part of a putative
solution, without assuming that its prime bases or exponents are fixed. -/
namespace OMA.CofactorHarmonic245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.LastDigit245212 (geom)

theorem phi_sigma (m : ℕ) : m.totient * σ 1 m ≤ m^2 := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p e hp =>
    cases e with
    | zero => simp
    | succ e =>
      rw [totient_prime_pow_succ hp,sigma_one_apply_prime_pow hp]
      have g := OMA.LastDigit245212.geom p (e+2) hp.pos
      have z := Nat.mul_le_mul_left (p^e)
        (show (∑ j∈range (e+2),p^j)*(p-1)≤p^(e+2) by omega)
      calc
        _ = p^e*((∑ j∈range (e+2),p^j)*(p-1)) := by ring
        _ ≤ _ := z
        _ = _ := by simp only [pow_succ];ring
  | coprime a b _ _ cop ia ib =>
    rw [totient_mul cop,isMultiplicative_sigma.map_mul_of_coprime cop,mul_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul ia ib

private theorem divisor_bounds {m : ℕ} (hm : 1 < m) :
    m*(σ 0 m)≤W m ∧ m<σ 1 m ∧ W m≤(σ 0 m)*(σ 1 m) := by
  have nz : m≠0 := by omega
  constructor
  · rw [w_apply,sigma_zero_apply]
    exact single_le_sum (f:=fun d : ℕ => d*d.divisors.card)
      (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self _ nz)
  constructor
  · rw [sigma_one_apply,←Nat.insert_self_properDivisors nz,sum_insert Nat.self_notMem_properDivisors]
    have h := single_le_sum (f:=fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
      (Nat.one_mem_properDivisors_iff_one_lt.mpr hm)
    omega
  · rw [w_apply,sigma_zero_apply,sigma_one_apply,mul_sum]
    exact sum_le_sum fun d hd => by
      rw [mul_comm m.divisors.card d]
      exact Nat.mul_le_mul_left d (Finset.card_le_card
        (Nat.divisors_subset_of_dvd nz (Nat.mem_divisors.mp hd).1))

/-- If h·m is a solution, the gap at the largest divisor of m is a
positive integer. The totient bound limits how much its other divisors
can contribute. -/
theorem gap {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    W h*(σ 0 m)+σ 1 h < 2*(h*σ 0 h)*(σ 0 m) ∧
    2*(h*σ 0 h)*(σ 0 m)*m.totient ≤ (W h*σ 0 m+σ 1 h)*m := by
  have mp : 0 < m := by omega
  have s := sigma_pos 1 h hh.ne'
  have b := OMA.Abundance245212.balance (mul_ne_zero hh.ne' mp.ne') eqn
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop] at b
  obtain ⟨l,r,u⟩ := divisor_bounds hm
  constructor
  · apply Nat.lt_of_mul_lt_mul_right (a:=m)
    nlinarith only [b,Nat.mul_le_mul_left (W h) l,Nat.mul_lt_mul_of_pos_left r s]
  · apply Nat.le_of_mul_le_mul_right _ mp
    have v := Nat.mul_le_mul_right m.totient (Nat.mul_le_mul_left (W h) u)
    have w := Nat.mul_le_mul_left (W h*σ 0 m+σ 1 h) (phi_sigma m)
    nlinarith only [congrArg (fun t : ℕ => t*m.totient) b,v,w]

/-- Uniform bound independent of the prime exponents inside m. -/
theorem totient_gap {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    (2*(h*σ 0 h)-W h)*m ≤ 2*(h*σ 0 h)*(σ 1 h+1)*(m-m.totient) := by
  obtain ⟨strict,cap⟩ := gap hh hm cop eqn
  let H := 2*(h*σ 0 h)
  let A := W h
  let S := σ 1 h
  let L := σ 0 m
  change A*L+S < H*L at strict
  change H*L*m.totient ≤ (A*L+S)*m at cap
  change (H-A)*m ≤ H*(S+1)*(m-m.totient)
  have al : A≤H := by
    by_contra! no
    exact (not_le_of_gt strict) ((Nat.mul_le_mul_right L no.le).trans (Nat.le_add_right _ _))
  have D := Nat.sub_add_cancel al
  have E : S+1≤(H-A)*L := by nlinarith only [strict,congrArg (·*L) D]
  have mu := Nat.sub_add_cancel m.totient_le
  have bound : ((H-A)*L-S)*m≤H*L*(m-m.totient) := by
    have diff := Nat.sub_add_cancel (show S≤(H-A)*L by omega)
    nlinarith only [cap,congrArg (·*m*L) D,congrArg (·*m) diff,congrArg (H*L*·) mu]
  have low : (H-A)*L ≤ (S+1)*((H-A)*L-S) := by
    have diff := Nat.sub_add_cancel (show S≤(H-A)*L by omega)
    have one : 1≤(H-A)*L-S := by omega
    nlinarith only [diff,Nat.mul_le_mul_left S one]
  apply Nat.le_of_mul_le_mul_right _ (sigma_pos 0 m (by omega : m≠0))
  nlinarith only [Nat.mul_le_mul_right m low,Nat.mul_le_mul_left (S+1) bound]

private theorem union_bound (s : Finset ℕ) (hp : ∀ p∈s,0 < p) :
    1-(∏ p∈s,(1-(p:ℚ)⁻¹)) ≤ ∑ p∈s,(p:ℚ)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s out ih =>
    have pp : 0<p := hp p (mem_insert_self ..)
    have tail (q : ℕ) (hq : q∈s) := hp q (mem_insert_of_mem hq)
    have unit (q : ℕ) (hq : q∈s) : 0≤1-(q:ℚ)⁻¹ := by
      have pos : (1:ℚ)≤q := by exact_mod_cast tail q hq
      have v := (inv_le_one₀ (by linarith : (0:ℚ)<q)).mpr pos
      linarith
    have bound : (∏ q∈s,(1-(q:ℚ)⁻¹))≤1 :=
      prod_le_one (fun q hq => unit q hq) (fun _ _ => by simp)
    have p0 : (0:ℚ)≤(p:ℚ)⁻¹ := by positivity
    rw [prod_insert out,sum_insert out]
    nlinarith only [ih tail,mul_le_mul_of_nonneg_left bound p0]

private theorem to_mass {m D scale : ℕ} (hm : 0 < m) (gap : D*m ≤ scale*(m-m.totient)) :
    (D:ℚ) ≤ (scale:ℚ) * ∑ p∈m.primeFactors,(p:ℚ)⁻¹ := by
  have rat : (D:ℚ)*m≤(scale:ℚ)*((m:ℚ)-(m.totient:ℚ)) := by
    rw [←Nat.cast_sub m.totient_le]
    exact_mod_cast gap
  rw [Nat.totient_eq_mul_prod_factors m] at rat
  have mass := union_bound m.primeFactors (fun _ hp => Nat.pos_of_mem_primeFactors hp)
  change (D:ℚ)≤(scale:ℚ)*_
  apply le_of_mul_le_mul_left (a:=(m:ℚ)) _ (by exact_mod_cast (show 0 < m by omega))
  nlinarith only [rat,mul_le_mul_of_nonneg_left mass (by positivity : 0≤(m:ℚ)*scale)]

/-- The distinct new primes must contribute a positive, explicit total
reciprocal mass determined solely by the known factor h. -/
theorem reciprocals {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ((2*(h*σ 0 h)-W h:ℕ):ℚ) ≤
      (2*(h*σ 0 h)*(σ 1 h+1):ℕ) * ∑ p∈m.primeFactors,(p:ℚ)⁻¹ :=
  to_mass (by omega) (totient_gap hh hm cop eqn)

/-- If the remaining exponents are prescribed, use their actual divisor
count to sharpen the lower bound. Its numerator is a positive integer. -/
theorem count_sensitive {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    let H := 2*(h*σ 0 h)*(σ 0 m)
    let A := W h*σ 0 m+σ 1 h
    0<H-A ∧ ((H-A:ℕ):ℚ) ≤ (H:ℚ)*∑ p∈m.primeFactors,(p:ℚ)⁻¹ := by
  obtain ⟨l,c⟩:=gap hh hm cop eqn
  dsimp only
  refine ⟨by omega,to_mass (by omega) ?_⟩
  have d := Nat.sub_add_cancel l.le
  have f := Nat.sub_add_cancel m.totient_le
  nlinarith only [c,congrArg (·*m) d,congrArg ((2*(h*σ 0 h)*(σ 0 m))*·) f]

private theorem from_mass {r H D m : ℕ} (lower : ∀ p∈m.primeFactors,r≤p)
    (mass : (D:ℚ)≤(H:ℚ)*∑ p∈m.primeFactors,(p:ℚ)⁻¹) : r*D ≤ m.primeFactors.card*H := by
  have per (p : ℕ) (hp : p∈m.primeFactors) : (r:ℚ)*(p:ℚ)⁻¹≤1 := by
    rw [←div_eq_mul_inv,div_le_one (by exact_mod_cast Nat.pos_of_mem_primeFactors hp : (0:ℚ)<p)]
    exact_mod_cast lower p hp
  have cap := sum_le_sum per
  simp only [←mul_sum,sum_const,nsmul_eq_mul,mul_one] at cap
  exact_mod_cast (show (r:ℚ)*D≤(m.primeFactors.card:ℚ)*H by
    nlinarith only [mul_le_mul_of_nonneg_left mass (Nat.cast_nonneg r),
      mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg H)])

/-- Taking r to be the least new prime gives an integer bound linear
in the number of remaining prime factors and independent of all exponents. -/
theorem least_prime {h m r : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (lower : ∀ p∈m.primeFactors,r≤p) (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    r*(2*(h*σ 0 h)-W h) ≤ m.primeFactors.card*(2*(h*σ 0 h)*(σ 1 h+1)) :=
  from_mass lower (reciprocals hh hm cop eqn)

end OMA.CofactorHarmonic245212

end

section

/- Explicit simultaneous base and exponent bounds for at least one
odd prime power of any solution with fixed dyadic exponent and rank. -/
namespace OMA.CofactorEffectiveOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.CofactorEulerSeparation245212
open OMA.CofactorEffectiveAtom245212
open scoped ArithmeticFunction.sigma

def height (h r : ℕ) := threshold (W h) (σ 1 h) r
def primeHeight (h r : ℕ) :=
  let H:=2*(h*σ 0 h)
  max (height h r+1) (r*H*(σ 1 h+1)/(H-W h))

theorem original {h m : ℕ} (hh : 0<h) (hm : 1 < m) (cop : h.Coprime m)
    (apart : miss (W h) (2*(h*σ 0 h)) m.primeFactors)
    (eqn : OeisA245212.a (h*m)=(σ 1 (h*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight h m.primeFactors.card ∧ m.factorization p≤height h m.primeFactors.card := by
  classical
  let t:=m.primeFactors
  let p : t→ℕ:=Subtype.val
  let e (i : t):=m.factorization (p i)
  have mn : m≠0:=by omega
  have pr (i:t) : (p i).Prime:=prime_of_mem_primeFactors i.property
  have localCop (i:t) : h.Coprime (p i):=cop.of_dvd_right (dvd_of_mem_primeFactors i.property)
  have repr : total p e=m := (Nat.prod_primeFactors_coe_pow_factorization mn).symm
  let D:=h*σ 0 h
  have d0 : 0<D:=mul_pos hh (sigma_pos 0 h hh.ne')
  have sc:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=p) (e:=e) hh pr
    Subtype.val_injective localCop (repr ▸ eqn)
  have sx : (∏i,X (p i) (some (e i)))=∏x∈t,X x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>X x (some (m.factorization x)))
  have sy : (∏i,Y (p i) (some (e i)))=∏x∈t,Y x (some (m.factorization x)) :=
    t.prod_coe_sort (fun x=>Y x (some (m.factorization x)))
  rw [sx,sy] at sc
  change ((W h:ℚ)/D)*_+((σ 1 h:ℚ)/D)*_=2 at sc
  field_simp [show (D:ℚ)≠0 by exact_mod_cast d0.ne'] at sc
  have mass : (W h:ℚ)*(∏x∈t,X x (some (m.factorization x)))+
      (σ 1 h:ℚ)*(∏x∈t,Y x (some (m.factorization x)))=((2*D:ℕ):ℚ) := by push_cast;linarith only [sc]
  rcases alternative (W h) (σ 1 h) (2*D) t m.factorization (fun _ hp=>prime_of_mem_primeFactors hp) apart mass with
    short|⟨q,hq,pq,eq⟩
  · have ne : t.Nonempty := by
      exact ⟨m.minFac,(Nat.mem_primeFactors_of_ne_zero mn).mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd _⟩⟩
    let q:=t.min' ne
    have mem : q∈t:=t.min'_mem ne
    have bound:=OMA.CofactorHarmonic245212.least_prime (r:=q) hh hm cop (fun r hr=>t.min'_le r hr) eqn
    have g:=(OMA.CofactorHarmonic245212.gap hh hm cop eqn).1
    have below : W h<2*D := by
      by_contra! no
      have bad:=Nat.mul_le_mul_right (σ 0 m) no
      change W h*σ 0 m+σ 1 h<2*D*σ 0 m at g
      omega
    have qp : q≤t.card*(2*D)*(σ 1 h+1)/(2*D-W h) := by
      apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt below)).mpr
      simpa only [D,mul_assoc] using bound
    exact ⟨q,mem,qp.trans (le_max_right _ _),short q mem⟩
  · exact ⟨q,hq,pq.trans (le_max_left _ _),eq⟩

theorem dyadic {k m : ℕ} (hm : 1 < m) (odd : Odd m)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) :
    ∃p∈m.primeFactors,p≤primeHeight (2^k) m.primeFactors.card ∧
      m.factorization p≤height (2^k) m.primeFactors.card := by
  apply original (by positivity) hm ((Nat.coprime_two_left.mpr odd).pow_left k) _ eqn
  apply miss_odd (OMA.DyadicPower245212.dyadic_odd k) (even_two_mul _)
  intro p mem
  exact Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mem))

end OMA.CofactorEffectiveOriginal245212

end

section

/- Effective finiteness when the largest odd exponent length is at most a
fixed multiple of the square of the shortest. All primes and the dyadic
exponent can move. -/
namespace OMA.ThreeMovingFinite245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.ThreeMovingScalar245212
open scoped ArithmeticFunction.sigma Function

/-- Covers both the uniform cutoff and the finitely many small dyadic exponents. -/
def shortCap (c : ℕ) :=
  minimumCut + 9 + ∑ k ∈ range (4*c+1), OMA.CofactorEffectiveOriginal245212.height (2^k) 3

def countCap (c : ℕ) := (c*shortCap c^2)^3

/-- A finite sum of explicit heights avoids requiring their monotonicity. -/
def valueCap (c : ℕ) := ∑ t ∈ range (countCap c+1),
  2^OMA.DivisorHeight245212.exponentLimit t*OMA.DivisorHeight245212.coreLimit t

theorem bounded {c k m L : ℕ} (p e : Fin 3 → ℕ) (hp : ∀i,(p i).Prime)
    (op : ∀i,Odd (p i)) (inj : p.Injective) (he : ∀i,0<e i)
    (hm : 0 < m) (lengths : ∀i,m≤e i+1 ∧ e i+1≤L) (shape : L≤c*m^2)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    m ≤ shortCap c ∧ 2^k*total p e ≤ valueCap c := by
  classical
  have odd : Odd (total p e) := Nat.coprime_two_left.mp
    (Coprime.prod_right (fun i _ => (Nat.coprime_two_left.mpr (op i)).pow_right _))
  have dvd i : p i∣total p e := (dvd_pow_self _ (he i).ne').trans
    (dvd_prod_of_mem (fun j => p j^e j) (mem_univ i))
  have big : 1<total p e := (hp 0).one_lt.trans_le (Nat.le_of_dvd odd.pos (dvd 0))
  have image : (total p e).primeFactors=univ.image p := by
    ext q
    constructor
    · intro mem
      have pr:=prime_of_mem_primeFactors mem
      obtain ⟨i,_,di⟩:=(pr.prime.dvd_finsetProd_iff _).mp (dvd_of_mem_primeFactors mem :
        q∣∏i,p i^e i)
      exact mem_image.mpr ⟨i,mem_univ _,((prime_dvd_prime_iff_eq pr (hp i)).mp (pr.dvd_of_dvd_pow di)).symm⟩
    · rintro mem
      obtain ⟨i,_,rfl⟩:=mem_image.mp mem
      exact mem_primeFactors.mpr ⟨hp i,dvd i,odd.pos.ne'⟩
  have len (i) : (total p e).factorization (p i)=e i := by
    unfold total
    rw [Nat.factorization_prod_apply (fun j _=>pow_ne_zero _ (hp j).ne_zero),sum_eq_single i]
    · simp [Nat.factorization_pow,(hp i).factorization_self]
    · intro j _ ne
      simp [Nat.factorization_pow,(hp j).factorization, Finsupp.single_eq_of_ne (inj.ne ne.symm)]
    · simp
  have small : m ≤ shortCap c := by
    by_cases sk : k≤4*c
    · obtain ⟨q,mem,_,eq⟩:=OMA.CofactorEffectiveOriginal245212.dyadic big odd eqn
      rw [image,card_image_of_injective _ inj] at eq
      rw [image] at mem
      obtain ⟨i,_,rfl⟩:=mem_image.mp mem
      have ei : e i ≤ OMA.CofactorEffectiveOriginal245212.height (2^k) 3 := by simpa [len] using eq
      have sm:=single_le_sum (f:=fun j=>OMA.CofactorEffectiveOriginal245212.height (2^j) 3)
        (fun j _=>Nat.zero_le _) (mem_range.mpr (show k < 4*c+1 by omega))
      have mi:=(lengths i).1
      dsimp only [shortCap];omega
    · by_cases lt : m≤3
      · dsimp only [shortCap];omega
      have kp : 1≤k := by omega
      have comp : 4*max (max 1 k) L < max 1 k*m^2 := by
        rw [max_eq_right kp, mul_max_of_nonneg _ _ (by decide : (0:ℕ)≤4)]
        apply max_lt
        · calc
            4*k = k*4 := Nat.mul_comm _ _
            _ < _ := Nat.mul_lt_mul_of_pos_left (by nlinarith [Nat.mul_le_mul (show 4 ≤ m by omega) (show 4 ≤ m by omega)]) kp
        · calc
            4*L ≤ 4*(c*m^2) := Nat.mul_le_mul_left _ shape
            _ = (4*c)*m^2 := by ring
            _ < _ := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      have sh:=OMA.ThreeMovingOriginal245212.shortest p e hp op inj he hm lengths comp eqn
      dsimp only [shortCap];omega
  refine ⟨small,?_⟩
  have pair : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).Pairwise
      (Nat.Coprime on (fun i => p i^e i)) := by
    intro i _ j _ ne
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (inj.ne ne)).pow_left _).pow_right _
  have count : (total p e).divisors.card=∏i,(e i+1) := by
    rw [←sigma_zero_apply]
    simpa [total,sigma_zero_apply_prime_pow (hp _)] using
      IsMultiplicative.map_prod (fun i => p i^e i) (isMultiplicative_sigma (k:=0)) univ pair
  have lc : L≤c*shortCap c^2:=shape.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small _))
  have tc : (total p e).divisors.card≤countCap c := by
    rw [count]
    calc
      _ ≤ ∏_i : Fin 3,c*shortCap c^2 := prod_le_prod' (fun i _=>(lengths i).2.trans lc)
      _ = _ := by simp [countCap]
  have ⟨ke,co⟩:=OMA.DivisorHeight245212.effective_box odd big eqn
  exact (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) ke.le) co).trans
    (single_le_sum (f:=fun t=>2^OMA.DivisorHeight245212.exponentLimit t*OMA.DivisorHeight245212.coreLimit t)
      (fun _ _=>Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le tc)))

end OMA.ThreeMovingFinite245212

end




/- Largest-prime exponents -/

section

/- Integer separation when a large final prime power and a large dyadic
power occur together. All errors are kept as signed integers. -/
namespace OMA.LargeLastInteger245212

theorem zero {G R J U V A : ℤ} (gp : 1≤G) (rp : 0<R) (ap : 0≤A)
    (small : 4*(|U|+A)≤R) (lower : 0≤V) (upper : 4*V≤G)
    (idn : G*R*J=G*U+A+R*V) : J=0 := by
  have g0 : 0≤G:=by omega
  have gu : 4*(G*U+A)≤G*R := by
    have h:=mul_le_mul_of_nonneg_left small g0
    have m:=mul_le_mul_of_nonneg_left (le_abs_self U) g0
    have n:=mul_le_mul_of_nonneg_right gp ap
    nlinarith only [h,m,n]
  have gl : -(G*R)≤4*(G*U+A) := by
    have hh:=mul_le_mul_of_nonneg_left small g0
    have mm:=mul_le_mul_of_nonneg_left (neg_le_abs U) g0
    have ga:=mul_nonneg g0 ap
    nlinarith only [hh,mm,ga,ap]
  have rv:=mul_le_mul_of_nonneg_left upper rp.le
  have rl:=mul_nonneg rp.le lower
  have prod : 0<G*R:=mul_pos (by omega) rp
  by_contra! ne
  rcases lt_or_gt_of_ne ne with neg|pos
  · have jneg : J≤ -1:=by omega
    have bad:=mul_le_mul_of_nonneg_left jneg prod.le
    nlinarith only [idn,gl,rl,bad,prod]
  · have jpos : 1≤J:=by omega
    have bad:=mul_le_mul_of_nonneg_left jpos prod.le
    nlinarith only [idn,gu,rv,bad,prod]

end OMA.LargeLastInteger245212

end

section

/- Exact integer identity after rounding only the final prime and the
dyadic moment, with all other odd prime powers kept exact. -/
namespace OMA.LargeLastPhysical245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

def u (r : ℕ) := r-1
def B (r d : ℕ) := (d+1)*(u r)^2
def w (r d : ℕ) := r*((d+1)*u r-1)
def s (r : ℕ) := r*u r
def G (k : ℕ) := 2^(k+1)-1

theorem identity {h r k d : ℕ} (hp : 0<h) (ho : Odd h) (pr : r.Prime)
    (ro : Odd r) (cop : h.Coprime r)
    (eqn : OeisA245212.a (2^k*h*r^d)=(σ 1 (2^k*h*r^d):ℤ)) :
    let A : ℤ := W h
    let S : ℤ := σ 1 h
    let T : ℤ := h*σ 0 h
    let J : ℤ := (k+1)*T*(B r d)-k*A*(w r d)-S*(s r)
    let U : ℤ := k*A-(u r)*S
    let V : ℤ := (k+1)*(A*(w r d)-T*(B r d))
    (G k:ℤ)*r^d*J=(G k)*U+(k+1)*A+(r:ℤ)^d*V := by
  have c1 : (2^k).Coprime h := (coprime_two_left.mpr ho).pow_left k
  have c2 : (2^k*h).Coprime (r^d) := (((coprime_two_left.mpr ro).pow_left k).mul_left cop).pow_right d
  have pos : 0<2^k*h*r^d:=Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos k) hp) (pow_pos pr.pos _)
  have natbal:=OMA.Abundance245212.balance pos.ne' eqn
  rw [w_mult.map_mul_of_coprime c2,w_mult.map_mul_of_coprime c1,
    isMultiplicative_sigma.map_mul_of_coprime c2,isMultiplicative_sigma.map_mul_of_coprime c1,
    isMultiplicative_sigma.map_mul_of_coprime c2,isMultiplicative_sigma.map_mul_of_coprime c1,
    sigma_zero_apply_prime_pow prime_two,sigma_zero_apply_prime_pow pr] at natbal
  have bal:=congrArg ((↑):ℕ→ℤ) natbal
  push_cast at bal
  have zm:=OMA.ComplementaryLocal245212.binary k
  rw [zm.1,zm.2] at bal
  have m:=OMA.ComplementaryLocal245212.moments pr d
  have ru : 1≤(d+1)*u r:=mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt pr.one_lt)
  have gz : 1≤2^(k+1):=Nat.two_pow_pos _
  dsimp only
  unfold G B w s u
  unfold u at ru
  push_cast [Nat.cast_sub gz,Nat.cast_sub pr.pos,Nat.cast_sub ru]
  rw [pow_succ' (2:ℤ) k] at bal ⊢
  linear_combination -((r:ℤ)-1)^2*bal+
    ((1+(k:ℤ)*(2*2^k))*(W h:ℤ))*m.2+
    (((2:ℤ)*2^k-1)*(σ 1 h:ℤ)*((r:ℤ)-1))*m.1

end OMA.LargeLastPhysical245212

end

section

/- At the largest odd prime, the exponent is bounded almost additively
by the other exponents. This works with moving primes and moving dyadic order. -/
namespace OMA.LargestPrimeExponent245212
open Finset Nat ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem updates {p : ℕ} (pr : p.Prime) (e : ℕ) :
    σ 1 (p^(e+1))=p*σ 1 (p^e)+1 ∧
    W (p^(e+1))=p*W (p^e)+σ 1 (p^(e+1)) := by
  constructor
  · rw [sigma_one_apply_prime_pow pr,sigma_one_apply_prime_pow pr,sum_range_succ']
    simp only [pow_succ',←mul_sum,pow_zero]
  · rw [w_pow pr,w_pow pr,sigma_one_apply_prime_pow pr,
      sum_range_succ' (fun j=>p^j*(j+1)) (e+1),sum_range_succ' (fun j=>p^j) (e+1)]
    simp only [pow_zero,zero_add,mul_one,pow_succ']
    rw [←add_assoc]
    congr 1
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i _;ring

theorem local_bounds {p : ℕ} (pr : p.Prime) (e : ℕ) :
    σ 1 (p^e)≤(p+1)^e ∧ W (p^e)≤(p+1)^(e+1) ∧ W (p^e)≤(2*p+1)^e := by
  induction e with
  | zero=>simp [w_mult.map_one]
  | succ e ih=>
    obtain ⟨s,w⟩:=updates pr e
    have pp : 0 < (p+1)^e:=pow_pos (Nat.succ_pos _) _
    have sBound : σ 1 (p^(e+1))≤(p+1)^(e+1) := by
      rw [s,pow_succ];nlinarith only [Nat.mul_le_mul_left p ih.1,pp]
    have s2 : σ 1 (p^(e+1))≤(p+1)*(2*p+1)^e := by
      calc
        _ ≤ (p+1)^(e+1) := sBound
        _ = (p+1)*(p+1)^e := pow_succ' _ _
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    refine ⟨sBound,?_,?_⟩
    · rw [w,pow_succ (p+1) (e+1)]
      nlinarith only [Nat.mul_le_mul_left p ih.2.1,sBound]
    · rw [w,pow_succ (2*p+1) e]
      nlinarith only [Nat.mul_le_mul_left p ih.2.2,s2]

private theorem weighted_pos {h : ℕ} (pos : 0 < h) : 0<W h := by
  rw [w_apply]
  exact sum_pos' (fun _ _=>Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr pos.ne',by simp⟩

/-- Strictness at the last coordinate saves one unit in the exponent. -/
private theorem compare {h P c E : ℕ} (pos : 0 < h) (pr : P.Prime) (odd : P≠2)
    (cop : h.Coprime P) (eqn : OeisA245212.a (h*P^c)=(σ 1 (h*P^c):ℤ))
    (wa : W h≤P^(E+1)) (sb : σ 1 h≤P^E) : c≤E := by
  have pb:=OMA.PrimePowerDiv245212.cofactor_bound pos pr odd cop c eqn
  have sp:=sigma_pos 1 h pos.ne'
  have wp:=weighted_pos pos
  have pp:=pr.one_lt
  have prod : (P-1)*σ 1 h<P^(E+1) := by
    rw [pow_succ']
    exact (Nat.mul_le_mul_left _ sb).trans_lt (Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos pr.pos _))
  have lt : ((W h:ℤ)-((P:ℤ)-1)*(σ 1 h:ℤ)).natAbs<P^(E+1) := by
    have v : 0<(P-1)*σ 1 h:=Nat.mul_pos (by omega) sp
    have z : ((P-1)*σ 1 h:ℕ)=((P:ℤ)-1)*(σ 1 h:ℤ) := by push_cast [Nat.cast_sub pr.pos];rfl
    apply Int.ofNat_lt.mp
    rw [Int.natCast_natAbs,abs_lt]
    constructor <;> omega
  by_contra! no
  exact (pb.trans_lt lt).not_ge (Nat.pow_le_pow_right pr.pos no)

def extra (p q P : ℕ) := if P<2*p+1 ∧ P<2*q+1 then 1 else 0

theorem triple_of_power {k j p q P a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : P.Prime)
    (op : 3≤p) (pq : p<q) (qr : q<P) (base : 5^k≤P^j)
    (eqn : OeisA245212.a (2^k*p^a*q^b*P^c)=(σ 1 (2^k*p^a*q^b*P^c):ℤ)) :
    c≤j+a+b+extra p q P := by
  have twoP : (2^k).Coprime p:=((coprime_primes prime_two pp).mpr (by omega)).pow_left k
  have twoQ : (2^k).Coprime q:=((coprime_primes prime_two qp).mpr (by omega)).pow_left k
  have twoR : (2^k).Coprime P:=((coprime_primes prime_two rp).mpr (by omega)).pow_left k
  have smallQ:= ((coprime_primes pp qp).mpr pq.ne).pow_left a
  have smallR:= ((coprime_primes pp rp).mpr (pq.trans qr).ne).pow_left a
  have midR:= ((coprime_primes qp rp).mpr qr.ne).pow_left b
  have cube:=local_bounds prime_two k
  have sw : W (2^k)≤P^j:=cube.2.2.trans base
  have ss : σ 1 (2^k)≤P^j:=cube.1.trans ((Nat.pow_le_pow_left (by decide : 2+1≤5) _).trans base)
  have small {z : ℕ} (pz : z.Prime) (lt : z<P) (n : ℕ) :
      σ 1 (z^n)≤P^n ∧ W (z^n)≤P^(n+1) ∧ (2*z+1≤P → W (z^n)≤P^n) := by
    obtain ⟨s,w,u⟩:=local_bounds pz n
    exact ⟨s.trans (Nat.pow_le_pow_left lt _),w.trans (Nat.pow_le_pow_left lt _),
      fun le=>u.trans (Nat.pow_le_pow_left le _)⟩
  obtain ⟨ps,pw,pt⟩:=small pp (pq.trans qr) a
  obtain ⟨qs,qw,qt⟩:=small qp qr b
  apply compare (by have :=pp.pos;have :=qp.pos;positivity) rp (by omega)
    ((twoR.mul_left smallR).mul_left midR) eqn
  · rw [w_mult.map_mul_of_coprime ((twoQ.mul_left smallQ).pow_right b),
      w_mult.map_mul_of_coprime (twoP.pow_right a)]
    by_cases near : P<2*p+1 ∧ P<2*q+1
    · simp only [extra,if_pos near]
      simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using Nat.mul_le_mul (Nat.mul_le_mul sw pw) qw
    · simp only [extra,if_neg near,add_zero]
      rcases not_and_or.mp near with far|far
      · simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using Nat.mul_le_mul (Nat.mul_le_mul sw (pt (by omega))) qw
      · simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using Nat.mul_le_mul (Nat.mul_le_mul sw pw) (qt (by omega))
  · rw [isMultiplicative_sigma.map_mul_of_coprime ((twoQ.mul_left smallQ).pow_right b),
      isMultiplicative_sigma.map_mul_of_coprime (twoP.pow_right a)]
    apply (Nat.mul_le_mul (Nat.mul_le_mul ss ps) qs).trans
    rw [←pow_add,←pow_add]
    exact Nat.pow_le_pow_right rp.pos (Nat.le_add_right _ _)

theorem triple {k j t p q P a b c : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : P.Prime)
    (op : 3≤p) (pq : p<q) (qr : q<P) (scale : 5^t≤P) (dyad : k≤t*j)
    (eqn : OeisA245212.a (2^k*p^a*q^b*P^c)=(σ 1 (2^k*p^a*q^b*P^c):ℤ)) :
    c≤j+a+b+extra p q P := by
  apply triple_of_power pp qp rp op pq qr _ eqn
  exact (Nat.pow_le_pow_right (by decide : 0<5) dyad).trans (by
    rw [pow_mul];exact Nat.pow_le_pow_left scale _)

end OMA.LargestPrimeExponent245212

end

section

/- Both error denominators dominate the one unperturbed integer coefficient
when the largest prime has exponent greater than 4(a+b)+31. -/
namespace OMA.LargeLastSize245212
open Nat OMA.LargeLastPhysical245212

theorem sizes {r k d n A S T : ℕ} (r5 : 5≤r) (cap : k<2*r) (short : d+1≤2*k)
    (aA : A≤r^(n+2)) (sA : S≤A) (tA : T≤A) (long : n+10≤d)
    (dyad : r^(n+10)≤2^k) :
    4*(k*A+(u r)*S+(k+1)*A)≤r^d ∧
    4*((k+1)*(A*w r d+T*B r d))≤G k := by
  have r1 : 1≤r:=by omega
  have rr : r*r≥5*r:=Nat.mul_le_mul_right r r5
  have kk : k+1≤r^2 := by rw [sq];omega
  have dcap : d+1≤r^2:=by rw [sq];omega
  have wcap : w r d≤r^4 := by
    dsimp [w,u]
    calc
      _ ≤ r*((d+1)*r) := Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
      _ ≤ r*(r^2*r) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ dcap)
      _ = _ := by ring
  have bcap : B r d≤r^4 := by
    dsimp [B,u]
    exact (Nat.mul_le_mul dcap (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)).trans_eq (by ring)
  have up := Nat.mul_le_mul (show u r≤r from Nat.sub_le _ _) (sA.trans aA)
  have ka := Nat.mul_le_mul (by omega : k≤r^2) aA
  have kua := Nat.mul_le_mul kk aA
  have single : r*r^(n+2)≤r^2*r^(n+2) := Nat.mul_le_mul_right _ (Nat.le_self_pow (by decide : 2≠0) _)
  have rmin : 12≤r^2 := (by decide : 12≤5^2).trans (Nat.pow_le_pow_left r5 _)
  have sum : 4*(k*A+(u r)*S+(k+1)*A) ≤ r^(n+6) := by
    calc
      _ ≤ 12*(r^2*r^(n+2)) := by omega
      _ ≤ r^2*(r^2*r^(n+2)) := Nat.mul_le_mul_right _ rmin
      _ = _ := by rw [show n+6=n+2+2+2 by omega,pow_add,pow_add];ring
  have big := Nat.add_le_add (Nat.mul_le_mul aA wcap) (Nat.mul_le_mul (tA.trans aA) bcap)
  have endcap : 4*((k+1)*(A*w r d+T*B r d))≤r^(n+10) := by
    calc
      _ ≤ 4*(r^2*(r^(n+2)*r^4+r^(n+2)*r^4)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul kk big)
      _ = 8*(r^(n+2)*r^4*r^2) := by ring
      _ ≤ r^2*(r^(n+2)*r^4*r^2) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [show n+10=n+2+8 by omega,pow_add];ring
  dsimp [G]
  rw [pow_succ]
  have g:=Nat.two_pow_pos k
  exact ⟨sum.trans (Nat.pow_le_pow_right r1 (by omega)),by omega⟩

end OMA.LargeLastSize245212

end

section

/- Elementary bounds on the two smaller prime-power factors. -/
namespace OMA.LargeLastCofactor245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.LargestPrimeExponent245212 (updates)

private theorem ratio {p a : ℕ} (pr : p.Prime) (ap : 0<a) : 3*σ 1 (p^a) ≤ 2*W (p^a) := by
  cases a with
  | zero=>omega
  | succ i=>
    induction i with
    | zero=>
      rw [sigma_one_apply_prime_pow pr,w_pow pr]
      simp [sum_range_succ]
      have:=pr.two_le;omega
    | succ i ih=>
      obtain ⟨s,w⟩:=OMA.LargestPrimeExponent245212.updates pr (i+1)
      rw [w,s]
      have b:=Nat.mul_le_mul_left p (ih (by omega))
      have z:=sigma_pos 1 (p^(i+1)) (pow_ne_zero _ pr.ne_zero)
      have lo:=Nat.mul_le_mul pr.two_le z
      nlinarith only [b,lo]

theorem pair {p q r a b : ℕ} (pp : p.Prime) (qp : q.Prime) (_p3 : 3≤p) (pq : p<q) (qr : q<r)
    (ap : 0<a) (bp : 0<b) :
    let h := p^a*q^b
    0<W h ∧ h*σ 0 h≤W h ∧ 2*σ 1 h≤W h ∧ W h≤r^(a+b+2) ∧
      σ 0 h=(a+1)*(b+1) := by
  let co:=(((Nat.coprime_primes pp qp).mpr pq.ne).pow_left a).pow_right b
  dsimp only
  rw [w_mult.map_mul_of_coprime co,isMultiplicative_sigma.map_mul_of_coprime co,
    isMultiplicative_sigma.map_mul_of_coprime co,sigma_zero_apply_prime_pow pp,sigma_zero_apply_prime_pow qp]
  have weight {z : ℕ} (prime : z.Prime) (e : ℕ) : (e+1)*z^e ≤ W (z^e) := by
    rw [w_pow prime,sum_range_succ];nlinarith only [Nat.zero_le (∑ i∈range e,z^i*(i+1))]
  have wp:=weight pp a
  have wq:=weight qp b
  have lp:=ratio pp ap
  have lq:=ratio qp bp
  have upperp:=(OMA.LargestPrimeExponent245212.local_bounds pp a).2.1.trans
    (Nat.pow_le_pow_left (by omega : p+1≤r) _)
  have upperq:=(OMA.LargestPrimeExponent245212.local_bounds qp b).2.1.trans
    (Nat.pow_le_pow_left (by omega : q+1≤r) _)
  refine ⟨Nat.mul_pos (lt_of_lt_of_le (Nat.mul_pos (Nat.succ_pos _) (pow_pos pp.pos a)) wp)
    (lt_of_lt_of_le (Nat.mul_pos (Nat.succ_pos _) (pow_pos qp.pos b)) wq),?_,?_,?_,rfl⟩
  · nlinarith only [Nat.mul_le_mul wp wq]
  · nlinarith only [Nat.mul_le_mul lp lq,Nat.zero_le (σ 1 (p^a)*σ 1 (q^b))]
  · convert Nat.mul_le_mul upperp upperq using 1
    rw [←pow_add];congr 1;omega

end OMA.LargeLastCofactor245212

end

section

/- The largest of three odd prime bases cannot carry an exponent
arbitrarily larger than the sum of the other two, uniformly in k. -/
namespace OMA.LargeLastOriginal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.LargeLastPhysical245212
open scoped ArithmeticFunction.sigma

theorem largest {k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p3 : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    d≤4*(a+b)+31 := by
  by_contra! long
  let h:=p^a*q^b
  let A:=W h
  let S:=σ 1 h
  let T:=h*σ 0 h
  let n:=a+b
  let D:=B r d
  let X:=w r d
  let Y:=s r
  have r5 : 5≤r:=by omega
  have r1:=rp.pos
  have po:=pp.odd_of_ne_two (by omega)
  have qo:=qp.odd_of_ne_two (by omega)
  have ro:=rp.odd_of_ne_two (by omega)
  have ho : Odd h:=(po.pow).mul (qo.pow)
  have op : Odd (h*r^d):=ho.mul ro.pow
  have localEq : OeisA245212.a (2^k*h*r^d)=(σ 1 (2^k*h*r^d):ℤ) := by
    simpa only [h,mul_assoc] using eqn
  have br : r∈(h*r^d).primeFactors := mem_primeFactors.mpr
    ⟨rp,dvd_mul_of_dvd_right (dvd_pow_self _ dp.ne') _,op.pos.ne'⟩
  have kcap:=OMA.DyadicLeast245212.exponent_lt_twice_prime op br (by simpa only [mul_assoc] using localEq)
  have cop : h.Coprime r:=(((coprime_primes pp rp).mpr (pq.trans qr).ne).pow_left a).mul_left
    (((coprime_primes qp rp).mpr qr.ne).pow_left b)
  have idn:=identity ho.pos ho rp ro cop localEq
  have ext1 : OMA.LargestPrimeExponent245212.extra p q r≤1 := by unfold OMA.LargestPrimeExponent245212.extra;split <;> decide
  have coarse:=OMA.LargestPrimeExponent245212.triple_of_power pp qp rp p3 pq qr (Nat.pow_le_pow_left r5 k) eqn
  have d2 : d+1≤2*k := by omega
  have dyad : r^(n+10)≤2^k := by
    by_contra! small
    have fives : 5^k ≤ r^(3*(n+10)) := calc
      _ ≤ (2^3)^k := Nat.pow_le_pow_left (by decide) _
      _ = (2^k)^3 := by rw [←pow_mul,←pow_mul,mul_comm 3 k]
      _ ≤ (r^(n+10))^3 := Nat.pow_le_pow_left small.le _
      _ = _ := by rw [←pow_mul,mul_comm]
    have sharper:=OMA.LargestPrimeExponent245212.triple_of_power pp qp rp p3 pq qr fives eqn
    dsimp [n] at sharper;omega
  have cf:=OMA.LargeLastCofactor245212.pair pp qp p3 pq qr ap bp
  change 0<A ∧ T≤A ∧ 2*S≤A ∧ A≤r^(n+2) ∧ σ 0 h=(a+1)*(b+1) at cf
  obtain ⟨apos,tA,sA,aCap,tau⟩:=cf
  have sz:=OMA.LargeLastSize245212.sizes (A:=A) (T:=T) (S:=S) r5 kcap d2 aCap
    (by omega) tA (by dsimp [n];omega) dyad
  have wden : D≤X := by
    have rpos := Nat.sub_add_cancel (by omega : 1≤r)
    have du : 1≤(d+1)*(r-1) := Nat.mul_pos (Nat.succ_pos _) (by omega)
    have sub:=Nat.sub_add_cancel du
    have delta:=Nat.mul_le_mul (by omega : 2≤d+1) (le_refl (r-1))
    dsimp [D,X,B,w,u]
    nlinarith only [rpos,congrArg ((r:ℕ)*·) sub,congrArg (fun z=> (d+1)*(r-1)*z) rpos,delta,r5]
  let J:ℤ:=(k+1)*(T:ℤ)*D-k*(A:ℤ)*X-S*(Y:ℤ)
  let U:ℤ:=(k:ℤ)*A-(u r:ℤ)*S
  let V:ℤ:=((k:ℤ)+1)*((A:ℤ)*X-T*(D:ℤ))
  have rposZ : (0:ℤ)<(r:ℤ)^d:=by have:=rp.pos;positivity
  have gp : 1≤G k := by dsimp [G];rw [pow_succ];have:=Nat.two_pow_pos k;omega
  have vz : 0≤V := by
    have zz : (T:ℤ)*D≤(A:ℤ)*X:=by exact_mod_cast Nat.mul_le_mul tA wden
    dsimp [V];positivity
  have mag : |U|≤(k*A+u r*S:ℕ):=by
    change |(k:ℤ)*A-(u r:ℤ)*S|≤_
    rw [abs_le];push_cast
    constructor <;> nlinarith only [Nat.cast_nonneg (k*A) (α:=ℤ),Nat.cast_nonneg (u r*S) (α:=ℤ)]
  have sm : 4*(|U|+((k:ℤ)+1)*A)≤(r:ℤ)^d := by
    have mg : 4*(((k*A+u r*S:ℕ):ℤ)+(k+1)*A) ≤ (r:ℤ)^d := by exact_mod_cast sz.1
    linarith only [mag,mg]
  have sm' : 4*V≤(G k:ℤ) := by
    have mg : (4:ℤ)*((k+1)*((A:ℤ)*X+T*(D:ℤ)))≤G k := by exact_mod_cast sz.2
    have extra : 0≤((k:ℤ)+1)*(T*D:ℕ):=by positivity
    push_cast at extra
    dsimp [V];nlinarith only [extra,mg]
  change (G k:ℤ)*r^d*J=(G k)*U+((k:ℤ)+1)*A+(r:ℤ)^d*V at idn
  have Z:=OMA.LargeLastInteger245212.zero (by exact_mod_cast gp) rposZ (by positivity) sm vz sm' idn
  have natJ : (k+1)*T*D=k*A*X+S*Y := by
    dsimp [J] at Z
    exact_mod_cast (show ((k:ℤ)+1)*T*D=k*(A:ℤ)*X+S*(Y:ℤ) by linarith only [Z])
  have near : r≤2*k+1 := by
    by_contra! far
    have dv : r∣(k+1)*T*D := natJ ▸ dvd_add
      (dvd_mul_of_dvd_right (dvd_mul_right r _) _) (dvd_mul_of_dvd_right (dvd_mul_right r _) _)
    have none (v : ℕ) (vpos : 0<v) (vlt : v<r) := Nat.not_dvd_of_pos_of_lt vpos vlt
    have kk:=none (k+1) (by omega) (by omega)
    have aa:=none (a+1) (by omega) (by omega)
    have bb:=none (b+1) (by omega) (by omega)
    have dd:=none (d+1) (by omega) (by omega)
    have uu:=none (u r) (by dsimp [u];omega) (by dsimp [u];omega)
    have cr : ¬r∣h:=rp.coprime_iff_not_dvd.mp cop.symm
    dsimp [T,D,B] at dv
    rw [tau] at dv
    rcases rp.dvd_mul.mp dv with left|right
    · rcases rp.dvd_mul.mp left with hit|hit
      · exact kk hit
      rcases rp.dvd_mul.mp hit with hit|hit
      · exact cr hit
      exact (rp.dvd_mul.mp hit).elim aa bb
    · exact (rp.dvd_mul.mp right).elim dd (fun w=>uu (rp.dvd_of_dvd_pow w))
  have positive : 0≤U := by
    have ub : u r≤2*k := by dsimp [u];omega
    have start : u r*S≤k*A := (Nat.mul_le_mul_right S ub).trans
      ((show 2*k*S=k*(2*S) by ring) ▸ Nat.mul_le_mul_left k sA)
    exact sub_nonneg.mpr (by exact_mod_cast start)
  rw [Z,mul_zero] at idn
  have ga : 0≤(G k:ℤ)*U:=mul_nonneg (by positivity) positive
  have wa : 0<((k:ℤ)+1)*A:=mul_pos (by positivity) (by exact_mod_cast apos)
  have ra : 0≤(r:ℤ)^d*V:=mul_nonneg rposZ.le vz
  linarith only [idn,ga,wa,ra]

end OMA.LargeLastOriginal245212

end

section

/- Effective finiteness from comparison of just the two lower-base
exponent lengths with the shortest length in the entire configuration. -/
namespace OMA.LargeLastSector245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma

theorem bounded {c k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p3 : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (shape : max (a+1) (b+1) ≤ c*(min (min (a+1) (b+1)) (d+1))^2)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    2^k*p^a*q^b*r^d ≤ OMA.ThreeMovingFinite245212.valueCap (20*c) := by
  let P : Fin 3→ℕ:=![p,q,r]
  let E : Fin 3→ℕ:=![a,b,d]
  let m:=min (min (a+1) (b+1)) (d+1)
  let t:=max (a+1) (b+1)
  have hD:=OMA.LargeLastOriginal245212.largest pp qp rp p3 pq qr ap bp dp eqn
  have pr (i) : (P i).Prime:=by fin_cases i <;> simp [P,pp,qp,rp]
  have op (i) : Odd (P i):=by apply (pr i).odd_of_ne_two;fin_cases i <;> simp [P] <;> omega
  have inj : P.Injective:=by
    intro i j he;fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have pos (i):0<E i:=by fin_cases i <;> simpa [E] using (show 0<_ by first | exact ap | exact bp | exact dp)
  have lens (i):m≤E i+1 ∧ E i+1≤20*t := by fin_cases i <;> simp [E,m,t] <;> omega
  have repr : 2^k*total P E=2^k*p^a*q^b*r^d := by simp [total,Fin.prod_univ_three,P,E,mul_assoc]
  have result:=OMA.ThreeMovingFinite245212.bounded P E pr op inj pos (show 0 < m by dsimp [m];omega) lens
    (show 20*t≤(20*c)*m^2 by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 20 shape)
    (by rw [repr];exact eqn)
  simpa only [repr] using result.2

end OMA.LargeLastSector245212

end




/- Two freely moving long exponents -/

section

/- Local rounding with one exactly retained prime allowed. -/
namespace OMA.TwoTallLocal245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212 OMA.ThreeMovingLocal245212
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingLocal245212 (quotients)

def Dn (p e : ℕ) : Option Bool → ℕ
  | none => (e+1)*p^e
  | some b => den p e b
def Nx (p e : ℕ) : Option Bool → ℕ
  | none => W (p^e)
  | some b => xn p e b
def Ny (p e : ℕ) : Option Bool → ℕ
  | none => σ 1 (p^e)
  | some b => yn p e b
def xx' (p e : ℕ) : Option Bool → ℚ
  | none => X p (some e)
  | some b => xx p e b
def yy' (p e : ℕ) : Option Bool → ℚ
  | none => Y p (some e)
  | some b => yy p e b
theorem Dpos {p : ℕ} (hp : p.Prime) (e : ℕ) (mode : Option Bool) : 0<Dn p e mode := by
  cases mode with
  | none =>exact Nat.mul_pos (Nat.succ_pos _) (pow_pos hp.pos _)
  | some b=>exact den_pos hp.two_le e b

theorem moments {p : ℕ} (hp : p.Prime) (e : ℕ) (mode : Option Bool) :
    xx' p e mode*(Dn p e mode:ℕ)=Nx p e mode ∧ yy' p e mode*(Dn p e mode:ℕ)=Ny p e mode := by
  cases mode with
  | none =>simpa [xx',yy',Dn,Nx,Ny,mul_assoc] using And.intro (x_factor hp e) (y_factor hp e)
  | some b=>
    have dp : (den p e b:ℚ)≠0:=by exact_mod_cast (den_pos hp.two_le e b).ne'
    simp [xx',yy',Dn,Nx,Ny,xx,yy,div_mul_cancel₀ _ dp]

theorem ranges {p e : ℕ} (hp : p.Prime) (pe : 0<e) (mode : Option Bool) :
    1≤xx' p e mode ∧ xx' p e mode≤2 ∧ 0≤yy' p e mode ∧ yy' p e mode≤2/((e:ℚ)+1) := by
  have a (b : Bool):=bounds hp pe (Nat.succ_pos e) (le_refl (e+1)) b
  cases mode with
  | none =>simpa [xx',yy'] using And.intro (a false).1 (And.intro (a false).2.1
      (And.intro (a false).2.2.1 (a false).2.2.2.1))
  | some b=>simpa [xx',yy'] using (a b).2.2.2.2

theorem move {p e f g m k : ℕ} (hp : p.Prime) (pe : 0<e) (mp : 0 < m)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (small : b=true → 4*(p-1)<k*m)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (cap : (y*y')*(m:ℚ)≤4) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have gate : 4*u < (k:ℚ)*m := by
      have sc : (4:ℚ)*((p-1:ℕ):ℚ)<k*(m:ℚ) := by exact_mod_cast small rfl
      simpa [u,Nat.cast_sub hp.one_le] using sc
    have unc : u*(y*y')<(k:ℚ) := by
      apply lt_of_mul_lt_mul_right (a:=(m:ℚ)) _ (by positivity)
      nlinarith only [gate,mul_le_mul_of_nonneg_left cap us]
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_lt_mul_of_pos_left unc g0,mul_le_mul_of_nonneg_left xl fm.le,fg]
    have q:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]

end OMA.TwoTallLocal245212

end

section

/- Cleared moments and the restriction on every retained prime. -/
namespace OMA.TwoTallGap245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212

structure Family where
  p : Fin 3→ℕ
  e : Fin 3→ℕ
  k : ℕ
  m : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 0<k
  mp : 0 < m
  long : ∀i,i≠2 → m≤e i+1
  cap : ∀i,e i+1≤L
  inj : p.Injective
  comparable : 4*max k L < k*m

def exactX (c : Family) (i : Fin 3) := X (c.p i) (some (c.e i))
def exactY (c : Family) (i : Fin 3) := Y (c.p i) (some (c.e i))
def x' (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) := xx' (c.p i) (c.e i) (b i)
def y' (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) := yy' (c.p i) (c.e i) (b i)
def dust (c : Family) (b : Fin 3→Option Bool) := ∏i,Dn (c.p i) (c.e i) (b i)
def NX (c : Family) (b : Fin 3→Option Bool) := ∏i,Nx (c.p i) (c.e i) (b i)
def NY (c : Family) (b : Fin 3→Option Bool) := ∏i,Ny (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin 3→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family) (b : Fin 3→Option Bool) : 0<dust c b :=
  prod_pos (fun i _=>Dpos (c.prime i) _ _)

theorem clear (c : Family) (b : Fin 3→Option Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s


private theorem largest {c : Family} {b : Fin 3→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=some true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=some true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=Nx (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Nx (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Nx,OMA.ThreeMovingLocal245212.xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=Ny (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Ny (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Ny,OMA.ThreeMovingLocal245212.yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:=c.cap i'
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    change q∣Dn (c.p i') (c.e i') (b i') at v
    cases which : b i' with
    | none =>
      rw [which] at v
      rcases pr.dvd_mul.mp v with hit|hit
      · exact absent hit
      have same:=c.inj ((prime_dvd_prime_iff_eq pr (c.prime i')).mp (pr.dvd_of_dvd_pow hit))
      exact (by rw [←same,sh] at which; contradiction)
    | some bit =>
      cases bit with
      | false => rw [which] at v;exact absent v
      | true =>
        have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,which⟩
        have sz:=top i' mt
        rw [which] at v
        rcases pr.dvd_mul.mp v with bad|bad
        · exact absent bad
        · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
            (by omega) (pr.dvd_of_dvd_pow bad)


theorem retained {c : Family} {b : Fin 3→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := largest frac unit hit

end OMA.TwoTallGap245212

end

section

/- Strict descent in a mixed moment with only two long exponents. -/
namespace OMA.TwoTallGap245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212

private theorem descend (c : Family) (b : Fin 3→Option Bool) (f g : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (moving : ∀i,i≠2 → b i≠none)
    (small : ∀i,b i=some true → c.p i≤ max (c.k+1) c.L) :
    score f g (x' c b) (y' c b)<score f g (exactX c) (exactY c) := by
  let mix (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactY c i else y' c b i
  have adv (s : Finset (Fin 3)) {i} (fresh : i∉s) (bit : Bool) (bi : b i=some bit) :
      score f g (mix s) (miy s)<score f g (mix (insert i s)) (miy (insert i s)) := by
    have bound j : 1≤ mix s j ∧ 0≤ miy s j ∧ miy s j≤2/((c.e j:ℚ)+1) := by
      by_cases mem : j∈s
      · have v:=ranges (c.prime j) (c.positive j) none
        simpa only [mix,miy,if_pos mem,exactX,exactY,xx',yy'] using And.intro v.1 v.2.2
      · have v:=ranges (c.prime j) (c.positive j) (b j)
        simpa only [mix,miy,if_neg mem,x',y'] using And.intro v.1 v.2.2
    have product {j l : Fin 3} (jl : j≠l) : (miy s j*miy s l)*(c.m:ℚ)≤4 := by
      have den z : (0:ℚ)<(c.e z:ℚ)+1:=by positivity
      have L z : miy s z*((c.e z:ℚ)+1)≤2:=(le_div_iff₀ (den z)).mp (bound z).2.2
      have low (z : Fin 3) : (1:ℚ)≤(c.e z:ℚ)+1:=by have:=Nat.cast_nonneg (α:=ℚ) (c.e z);linarith
      have D z (lt : z≠2) : (c.m:ℚ)≤(c.e z:ℚ)+1:=by exact_mod_cast c.long z lt
      have mm : (c.m:ℚ)≤((c.e j:ℚ)+1)*((c.e l:ℚ)+1) := by
        by_cases j2 : j=2
        · have l2 : l≠2:=by intro h;exact jl (j2.trans h.symm)
          simpa using mul_le_mul (low j) (D l l2) (Nat.cast_nonneg c.m) (den j).le
        · simpa using mul_le_mul (D j j2) (low l) (by decide : (0:ℚ)≤1) (den j).le
      have co:=mul_le_mul (L j) (L l) (mul_nonneg (bound l).2.1 (den l).le) (by decide : (0:ℚ)≤2)
      nlinarith only [co,mul_le_mul_of_nonneg_left mm (mul_nonneg (bound j).2.1 (bound l).2.1)]
    have single {j l : Fin 3} (n : j≠i) (n' : l≠i) (jl : j≠l) :
        (f:ℚ)*mix s i*mix s j*mix s l+g*miy s i*miy s j*miy s l <
        f*mix (insert i s) i*mix (insert i s) j*mix (insert i s) l+
          g*miy (insert i s) i*miy (insert i s) j*miy (insert i s) l := by
      have size (inb : bit=true) : 4*(c.p i-1)<c.k*c.m := by
        have lim:=small i (inb ▸ bi)
        have before : c.p i-1≤ max c.k c.L := by omega
        exact (Nat.mul_le_mul_left _ before).trans_lt c.comparable
      have step:=move (c.prime i) (c.positive i) c.mp c.kp gp fg bit size
        (mix s j) (mix s l) (miy s j) (miy s l) (bound j).1 (bound l).1 (bound j).2.1 (bound l).2.1 (product jl)
      simpa [mix,miy,exactX,exactY,x',y',xx',yy',fresh,n,n',bi] using step
    dsimp [score]
    simp only [Fin.prod_univ_three]
    have choice : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choice with rfl|rfl|rfl
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=1) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=1) (by decide) (by decide) (by decide)
  obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp (moving 0 (by decide))
  obtain ⟨w,hw⟩ := Option.ne_none_iff_exists'.mp (moving 1 (by decide))
  have a:=adv ∅ (i:=0) (by decide) v hv
  have b1:=adv {0} (i:=1) (by decide) w hw
  have final : score f g (mix {1,0}) (miy {1,0})≤ score f g (mix univ) (miy univ) := by
    have setEq : insert (2:Fin 3) ({1,0} : Finset (Fin 3))=univ:=by decide
    cases h : b 2 with
    | some bit=> simpa only [setEq] using (adv {1,0} (i:=2) (by decide) bit h).le
    | none=>
      have xx : mix {1,0}=mix univ :=by funext i;fin_cases i <;> simp [mix,x',exactX,h,xx']
      have yy : miy {1,0}=miy univ :=by funext i;fin_cases i <;> simp [miy,y',exactY,h,yy']
      rw [xx,yy]
  simpa [mix,miy] using ((a.trans b1).trans_le final)

theorem nonzero (c : Family) (b : Fin 3→Option Bool) (f g l : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (moving : ∀i,i≠2 → b i≠none) (frac : f+g=(c.k+1)*l) (unit : ∀i,¬c.p i∣l)
    (actual : score f g (exactX c) (exactY c)≤(f+g:ℕ)) :
    (f+g)*dust c b ≠ f*NX c b+g*NY c b := by
  intro hit
  have less:=(descend c b f g gp fg moving (retained frac unit hit)).trans_le actual
  have val:=clear c b f g
  have id : ((f+g:ℕ):ℚ)*dust c b=((f*NX c b+g*NY c b:ℕ):ℚ) := by exact_mod_cast hit
  exact (ne_of_lt (mul_lt_mul_of_pos_right less (show (0:ℚ)<dust c b by exact_mod_cast dust_pos c b))) (val.trans id.symm)


end OMA.TwoTallGap245212

end

section

/- Integer growth estimates and an empty multiplicative interval for three bases and the third prime power. -/
namespace OMA.TwoTallScalar245212

def cut (x j : ℕ) := x^(16^j)

theorem cut_succ (x i : ℕ) : cut x (i+1)=(cut x i)^16 := by
  rw [cut,cut,pow_succ,pow_mul]

theorem cut_mono {x : ℕ} (pos : 1≤x) : Monotone (cut x) :=
  fun _ _ le=>Nat.pow_le_pow_right pos (Nat.pow_le_pow_right (by decide) le)

theorem empty_interval (x : ℕ) (hx : 1≤x) (p : Fin 4→ℕ) :
    ∃j : Fin 5,∀i, p i ≤ cut x j.val ∨ cut x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have:=Fintype.card_le_of_injective _ inj
  norm_num at this

def budget := 16^5

def base (k L : ℕ) := 128*(k+2)*(L+1)

-- The larger exponent covers substitution of the exact dyadic numerator.
def degree := (budget+4)*budget

def minimumCut := 64*(degree+1)^2

private theorem square_product (p m F : ℕ) : ((p^14*m^2)^F)^2=p^(28*F)*m^(4*F) := by
  rw [←pow_mul,mul_pow,←pow_mul,←pow_mul,show 14*(F*2)=28*F by ring,show 2*(F*2)=4*F by ring]

theorem scale {m k L p e : ℕ} (hp : 3≤p) (hk : k<2*p) (hm : minimumCut ≤ m)
    (comparable : L ≤ k*m^2) (low : m≤e+1) :
    (base k L)^degree ≤ p^e := by
  let F:=degree
  have fp : 1≤F := by decide
  change 64*(F+1)^2≤ m at hm
  have mp : 1≤ m:=by nlinarith only [hm,Nat.zero_le (F^2),Nat.zero_le F]
  have pp : 1≤p:=by omega
  have kcap : k+2≤4*p := by omega
  have Lcap : L+1≤3*p*m^2 := by
    have mpos:=Nat.mul_pos (show 0<p by omega) (pow_pos mp 2)
    nlinarith only [comparable,Nat.mul_le_mul_right (m^2) hk.le,mpos]
  have scale : base k L≤p^14*m^2 := by
    have sixteen : 1536≤p^12 := (by decide : 1536≤3^12).trans (Nat.pow_le_pow_left hp _)
    have b:=Nat.mul_le_mul kcap Lcap
    dsimp [base]
    nlinarith only [Nat.mul_le_mul_left 128 b,Nat.mul_le_mul_right (p^2*m^2) sixteen]
  have grow := OMA.ComplementarySize245212.absorb (d:=2*F) (b:=m) (by nlinarith only [hm,Nat.zero_le F])
  have poly : m^(4*F)≤p^m := (by convert grow using 1; ring : m^(4*F)≤2^m).trans (Nat.pow_le_pow_left (by omega) _)
  have gain : 28*F+m≤2*e := by
    nlinarith only [hm,low,Nat.zero_le (F^2)]
  apply (pow_le_pow_iff_left₀ (show 0≤(base k L)^degree from Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
  change ((base k L)^F)^2≤(p^e)^2
  calc
    _ ≤ ((p^14*m^2)^F)^2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left scale _) _
    _ = p^(28*F)*m^(4*F) := square_product p m F
    _ ≤ p^(28*F)*p^m := Nat.mul_le_mul_left _ poly
    _ = p^(28*F+m) := (pow_add ..).symm
    _ ≤ p^(2*e) := Nat.pow_le_pow_right pp gain
    _ = (p^e)^2 := by rw [mul_comm,pow_mul]

end OMA.TwoTallScalar245212

end

section

/- A missing interval among four ordered cutoffs makes the local tail
smaller than a nonzero integer's reciprocal denominator. -/
namespace OMA.TwoTallStep245212
open Nat Finset OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212 OMA.TwoTallGap245212 OMA.TwoTallScalar245212
open OMA.CofactorEffectiveAtom245212 (product_error)

private theorem integer_gap (c : Family) (bits : Fin 3→Option Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

private theorem difference (c : Family) (b : Fin 3→Option Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀ i t, b i=some t → N ≤ (if t then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤48*((f:ℚ)+g)/N := by
  have bp i := ranges (c.prime i) (c.positive i) (b i)
  have ex i := ranges (c.prime i) (c.positive i) none
  have er (i) : |exactX c i-x' c b i|≤2/(N:ℚ) ∧ |exactY c i-y' c b i|≤2/(N:ℚ) := by
    cases h:b i with
    | none=>simp [exactX,x',exactY,y',h,xx',yy'];positivity
    | some t=>simpa [exactX,x',exactY,y',h,xx',yy'] using error (c.prime i) (c.positive i) n0 t (space i t h)
  have eps : (0:ℚ)≤2/N := by positivity
  have one i : 2/((c.e i:ℚ)+1)≤2 := div_le_self (by decide) (by have:=Nat.cast_nonneg (α:=ℚ) (c.e i);linarith)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (ex i).1,(ex i).2.1,zero_le_one.trans (bp i).1,(bp i).2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactY c) (y' c b) eps
    (fun i _=>⟨(ex i).2.2.1,(ex i).2.2.2.trans (one i),(bp i).2.2.1,(bp i).2.2.2.trans (one i),(er i).2⟩)
  norm_num at x y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family) (f g l x : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (frac : f+g=(c.k+1)*l) (unit : ∀i,¬c.p i∣l)
    (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (powers : ∀i,i≠2 → x^budget≤(c.p i)^(c.e i))
    (actual : score f g (exactX c) (exactY c)≤(f+g:ℕ))
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^budget:ℕ):ℚ)) : False := by
  obtain ⟨j,band⟩:=empty_interval x (by omega) (Fin.snoc c.p (c.p 2^c.e 2))
  have bp (i:Fin 3) := band i.castSucc
  have bd:=band (Fin.last 3)
  simp only [Fin.snoc_castSucc] at bp
  simp only [Fin.snoc_last] at bd
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3) : Option Bool := if i=2 ∧ c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have moving i (ne:i≠2) : b i≠none:=by simp [b,ne]
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^budget:=cut_mono (by omega) (show j.val+1≤5 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        by_cases i2 : i=2
        · subst i;exact (bd.resolve_left (fun h=>off ⟨rfl,h⟩)).le
        · exact nb.trans (powers i i2)
      · simpa [lo] using ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^9 := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : i=2 ∧ c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode.2).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have nz:=nonzero c b f g l gp fg moving frac unit actual
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega

end OMA.TwoTallStep245212

end

section

/- Absolute bounds for the shortest of three moving odd prime exponents
if the longest is not too large. The dyadic exponent is unrestricted. -/
namespace OMA.TwoTallOriginal245212
open Nat Finset ArithmeticFunction OMA.TwoTallGap245212 OMA.TwoTallScalar245212
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)

def F (k : ℕ) := 1+k*2^(k+1)
def G (k : ℕ) := 2^(k+1)-1

private theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩

theorem physical (c : Family) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]

private theorem small_case (c : Family) (hp : ∀i,3≤c.p i) (hk : ∀i,c.k<2*c.p i) (high : minimumCut≤c.m)
    (exact : score (F c.k) (G c.k) (exactX c) (exactY c)=(F c.k+G c.k:ℕ)) : False := by
  let x:=base c.k c.L
  have big : 128≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have comp : c.L≤c.k*c.m^2 := by
    have small : c.L≤c.k*c.m:=by have:=c.comparable;omega
    exact small.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide : 2≠0) _))
  have powers i (ni : i≠2) : x^degree≤c.p i^c.e i := scale (hp i) (hk i) high comp (c.long i ni)
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.ThreeMovingLocal245212.bounds (c.prime i) (c.positive i) (Nat.succ_pos (c.e i)) (le_refl _) true
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤8 := calc
    _ ≤ ∏_i:Fin 3,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_cases ample : 8*(c.k+1)*x^budget≤G c.k
  · have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
      push_cast
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
    have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^budget:ℕ):ℚ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
      have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^budget:ℕ)≤1 := by
        apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
        have g0 : (8:ℚ)*(c.k+1)*(x^budget:ℕ)≤G c.k:=by exact_mod_cast ample
        push_cast at g0 ⊢
        nlinarith only [congrArg (·*(x:ℚ)^budget) id,g0,
          mul_le_mul_of_nonneg_right (show PX-1≤8 by linarith) (show 0≤((c.k:ℚ)+1)*x^budget by positivity)]
      exact (le_div_iff₀ (by exact_mod_cast pow_pos dx budget : (0:ℚ)<(x^budget:ℕ))).mpr h
    apply OMA.TwoTallStep245212.contradiction c c.k 1 1 x (by decide) (by simp) (by simp) _ big cf cl
      (fun i ni=>(Nat.pow_le_pow_right dx (show budget≤degree by decide)).trans (powers i ni)) below close
    intro i; exact Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt
  · let x':=x^(budget+4)
    have lift : x≤x':=Nat.le_self_pow (by omega : budget+4≠0) _
    have fcap : F c.k+G c.k≤x' := by
      have gcap : G c.k+1≤8*(c.k+1)*x^budget:=by omega
      have zid : 2^(c.k+1)=G c.k+1 := by dsimp [G];have:=Nat.two_pow_pos (c.k+1);omega
      rw [(identities c.k).2.1,zid]
      calc
        _ ≤ (c.k+1)*(8*(c.k+1)*x^budget) := Nat.mul_le_mul_left _ gcap
        _ = (c.k+1)*(8*((c.k+1)*x^budget)) := by ring
        _ ≤ x*(x*(x*x^budget)) := Nat.mul_le_mul cf (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ cf))
        _ = x^(budget+3) := by rw [pow_add];ring
        _ ≤ x' := Nat.pow_le_pow_right dx (by omega)
    apply OMA.TwoTallStep245212.contradiction c (F c.k) (G c.k) (2^(c.k+1)) x' r0
      (by have:=(identities c.k).2.2;omega) (identities c.k).2.1 _ (big.trans lift) fcap (cl.trans lift)
      (fun i ni=>by dsimp [x'];rw [←pow_mul];exact powers i ni) exact.le (by rw [exact,sub_self,abs_zero];positivity)
    intro i d
    have dv:=(c.prime i).dvd_of_dvd_pow d
    exact (Nat.not_dvd_of_pos_of_lt (by decide) (hp i)) dv

theorem shortest {k m L : ℕ} (p e : Fin 3→ℕ) (hp : ∀i,(p i).Prime) (op : ∀i,Odd (p i)) (inj : p.Injective)
    (ep : ∀i,0<e i) (kp : 0<k) (mp : 0 < m) (long : ∀i,i≠2 → m≤e i+1) (cap : ∀i,e i+1≤L)
    (comp : 4*max k L < k*m)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) : m < minimumCut := by
  by_contra! high
  let c : Family := ⟨p,e,k,m,L,hp,ep,kp,mp,long,cap,inj,comp⟩
  have p3 i : 3≤p i := by have:=(hp i).two_le;obtain ⟨j,ju⟩:=op i;omega
  have odd : Odd (total p e) := Nat.coprime_two_left.mp (Coprime.prod_right (fun i _=>(Nat.coprime_two_left.mpr (op i)).pow_right _))
  have inF i : p i∈(total p e).primeFactors := Nat.mem_primeFactors.mpr ⟨hp i,
    (dvd_pow_self _ (ep i).ne').trans (dvd_prod_of_mem (fun j=>p j^e j) (mem_univ i)),odd.pos.ne'⟩
  exact small_case c p3 (fun i=>OMA.DyadicLeast245212.exponent_lt_twice_prime odd (inF i) eqn) high (physical c k op inj eqn)

end OMA.TwoTallOriginal245212

end

section

/- Congruences for complete dyadic blocks in the weighted geometric sum. -/
namespace OMA.DyadicBlocks245212
open Finset Nat

def geom (p n : ℕ) := ∑ i∈range n,p^i
def weight (p n : ℕ) := ∑ i∈range n,p^i*(i+1)

theorem split_g (p m n : ℕ) : geom p (m+n)=geom p m+p^m*geom p n := by
  simp only [geom,sum_range_add,mul_sum,pow_add]

theorem split_w (p m n : ℕ) :
    weight p (m+n)=weight p m+p^m*(weight p n+m*geom p n) := by
  simp only [weight,geom,sum_range_add]
  congr 1
  simp only [mul_sum,←sum_add_distrib,pow_add]
  apply sum_congr rfl
  intro i _
  ring

theorem pow_block (p h : ℕ) (ho : Odd p) :
    p^(2^h) ≡ 1 [MOD 2^(h+1)] := by
  have cop := (Nat.coprime_two_right.mpr ho).pow_right (h+1)
  simpa only [Nat.totient_prime_pow_succ Nat.prime_two,Nat.reduceSub,mul_one] using
    Nat.ModEq.pow_totient cop

theorem div_geom (p : ℕ) (ho : Odd p) (h : ℕ) : 2^h ∣ geom p (2^h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, Nat.mul_two,split_g,←one_add_mul]
    have even := (ho.pow (n:=2^h)).add_one
    simpa [Nat.two_mul,add_comm] using Nat.mul_dvd_mul (even_iff_two_dvd.mp even) ih

theorem weight_block (p : ℕ) (ho : Odd p) (h : ℕ) :
    weight p (2^(h+1)) ≡ 2^h [MOD 2^(h+1)] := by
  induction h with
  | zero => simp [weight,sum_range_succ,Nat.ModEq]
  | succ h ih =>
    let N := 2^(h+1)
    have even : 2∣geom p N := (dvd_pow_self 2 (by omega : h+1≠0)).trans (div_geom p ho _)
    have off : N*geom p N ≡ 0 [MOD 2*N] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [mul_comm] using Nat.mul_dvd_mul_left N even
    have pp : p^N ≡ 1 [MOD 2*N] := by
      simpa only [N,pow_succ (2:ℕ) (h+1),mul_comm] using pow_block p (h+1) ho
    have twice : 2*weight p N ≡ N [MOD 2*N] := by
      simpa only [N,pow_succ' (2:ℕ) h] using ih.mul_left' 2
    have bridge := (Nat.ModEq.rfl (a:=weight p N)).add
      (pp.mul ((Nat.ModEq.rfl (a:=weight p N)).add off))
    change weight p (2^(h+1+1)) ≡ 2^(h+1) [MOD 2^(h+1+1)]
    rw [pow_succ' (2:ℕ) (h+1)]
    change weight p (2*N) ≡ N [MOD 2*N]
    rw [show 2*N=N+N by omega,split_w]
    simpa [Nat.two_mul] using bridge.trans (by simpa [Nat.two_mul] using twice)

theorem prime_block (p h a : ℕ) (hp : p.Prime) (ho : Odd p) :
    let N := 2^(h+1)
    let n := p^(a*N)
    n ≡ 1 [MOD N] ∧ ArithmeticFunction.sigma 0 n ≡ 1 [MOD N] ∧
      ArithmeticFunction.sigma 1 n ≡ 1 [MOD N] ∧
      OMA.Smooth245212.W n ≡ 1+a*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (pow_block p (h+1) ho).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have zeroG := Nat.modEq_zero_iff_dvd.mpr (div_geom p ho (h+1))
  have we := weight_block p ho h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]
    simpa only [one_pow] using p1.pow b
  have dz (b : ℕ) : b*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
  have blk (b : ℕ) : geom p (b*N) ≡ 0 [MOD N] ∧ weight p (b*N) ≡ b*2^h [MOD N] := by
    induction b with
    | zero => simp [geom,weight,Nat.ModEq]
    | succ b ih =>
      rw [Nat.succ_mul,split_g,split_w]
      constructor
      · simpa only [mul_zero,add_zero] using ih.1.add ((powr b).mul zeroG)
      · simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
          ih.2.add ((powr b).mul (we.add ((dz b).mul zeroG)))
  have times (b : ℕ) : b*N+1 ≡ 1 [MOD N] := (dz b).add_right 1
  refine ⟨powr a,?_,?_,?_⟩
  · rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]; exact times a
  · rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,sum_range_succ]
    simpa only [geom,N,zero_add] using (blk a).1.add (powr a)
  · rw [OMA.Smooth245212.w_pow hp,sum_range_succ]
    simpa only [weight,N,one_mul,add_comm 1] using (blk a).2.add ((powr a).mul (times a))

end OMA.DyadicBlocks245212

end

section

/- Exact power of two in a weighted sum of divisors of an odd prime power. -/
namespace OMA.WeightVal245212
open Finset OMA.Smooth245212 OMA.DyadicBlocks245212
open scoped ArithmeticFunction.sigma
open OMA.DyadicBlocks245212 (split_g)
open OMA.DyadicBlocks245212 (split_w)
open OMA.DyadicBlocks245212 (pow_block)

abbrev val (n : ℕ) := n.factorization 2
theorem val_odd {n : ℕ} (h : Odd n) : val n=0 :=
  Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.mp h; omega)

theorem identify {n h : ℕ} (nz : 0<n) (mod : n ≡ 2^h [MOD 2^(h+1)]) : val n=h := by
  have pp : 0<2^h := Nat.two_pow_pos _
  have bound : 2^h<2^(h+1) := by rw [pow_succ]; omega
  have low : 2^h∣n := Nat.modEq_zero_iff_dvd.mp
    ((mod.of_dvd (pow_dvd_pow _ (by omega))).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))
  have high : ¬2^(h+1)∣n := by
    intro d
    have bad := Nat.modEq_zero_iff_dvd.mp (mod.symm.trans (Nat.modEq_zero_iff_dvd.mpr d))
    exact bound.not_ge (Nat.le_of_dvd pp bad)
  have l := (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mp low
  have hi := mt (Nat.prime_two.pow_dvd_iff_le_factorization nz.ne').mpr high
  change n.factorization 2=h
  omega

theorem blocks (p : ℕ) (op : Odd p) (h u : ℕ) :
    let N := 2^(h+1)
    geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N] := by
  let N := 2^(h+1)
  have p1 : p^N ≡ 1 [MOD N] := (OMA.DyadicBlocks245212.pow_block p (h+1) op).of_dvd
    (pow_dvd_pow _ (by omega : h+1≤h+1+1))
  have gp := Nat.modEq_zero_iff_dvd.mpr (div_geom p op (h+1))
  have wp := weight_block p op h
  have powr (b : ℕ) : p^(b*N) ≡ 1 [MOD N] := by
    rw [Nat.mul_comm b N,pow_mul]; simpa only [one_pow] using p1.pow b
  dsimp only
  change geom p (u*N) ≡ 0 [MOD N] ∧ weight p (u*N) ≡ u*2^h [MOD N]
  induction u with
  | zero => simp [geom,weight,Nat.ModEq]
  | succ u ih =>
    have dz : u*N ≡ 0 [MOD N] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    rw [Nat.succ_mul,OMA.DyadicBlocks245212.split_g,OMA.DyadicBlocks245212.split_w]
    exact ⟨by simpa only [mul_zero,zero_add] using ih.1.add ((powr u).mul gp),
      by simpa only [zero_mul,add_zero,one_mul,Nat.succ_mul] using
        ih.2.add ((powr u).mul (wp.add (dz.mul gp)))⟩

private theorem even_weight {p t : ℕ} (odd : Odd p) (tp : 0<t) (even : Even t) :
    ∃ h, val t=h+1 ∧ weight p t ≡ 2^h [MOD 2^(h+1)] ∧ 2^(h+1)∣geom p t := by
  obtain ⟨k,u,ou,eq⟩ := Nat.exists_eq_two_pow_mul_odd tp.ne'
  cases k with
  | zero => simp only [pow_zero,one_mul] at eq; exact (Nat.not_even_iff_odd.mpr ou (eq ▸ even)).elim
  | succ h =>
    have prod : t=u*2^(h+1) := eq.trans (mul_comm _ _)
    have vv : val t=h+1 := by
      have vu := val_odd ou
      unfold val at vu ⊢
      rw [prod,Nat.factorization_mul ou.pos.ne' (by positivity),Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two,vu,zero_add]
    have b := blocks p odd h u
    dsimp only at b
    have o : u ≡ 1 [MOD 2] := by simpa [Nat.ModEq] using Nat.odd_iff.mp ou
    have reduced : u*2^h ≡ 2^h [MOD 2^(h+1)] := by
      simpa [pow_succ,mul_comm] using o.mul_right' (2^h)
    exact ⟨h,vv,prod ▸ b.2.trans reduced,prod ▸ Nat.modEq_zero_iff_dvd.mp b.1⟩

private theorem weight_pos {p t : ℕ} (ht : 0<t) : 0<weight p t :=
  sum_pos' (fun _ _=>Nat.zero_le _) ⟨0,mem_range.mpr ht,by simp⟩

/-- The valuation depends only on the exponent, even when the odd prime varies. -/
theorem weight_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    val (W (p^e))+1=val (e+1)+val (e+2) := by
  rw [w_pow hp]
  change val (weight p (e+1))+1=_
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have vo := val_odd (show Odd (e+2) from ev.add_one)
    rw [identify (weight_pos (by omega)) ww,vv,vo,Nat.add_zero]
  · have ev : Even (e+2) := od.add_one
    obtain ⟨h,vv,ww,_⟩ := even_weight odd (by omega) ev
    have d : 2^(h+1)∣e+2 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : e+2≠0)).mpr vv.ge
    have off : p^(e+1)*(e+2) ≡ 0 [MOD 2^(h+1)] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right d _)
    have next : weight p (e+2) ≡ weight p (e+1) [MOD 2^(h+1)] := by
      dsimp only [weight]
      rw [sum_range_succ _ (e+1)]
      simpa only [weight,add_zero] using (Nat.ModEq.refl (weight p (e+1))).add off
    rw [identify (weight_pos (by omega)) (next.symm.trans ww),val_odd od,vv,zero_add]

theorem sigma_local {p : ℕ} (hp : p.Prime) (odd : Odd p) (e : ℕ) :
    2^val (e+1)∣ArithmeticFunction.sigma 1 (p^e) := by
  rcases Nat.even_or_odd (e+1) with ev|od
  · obtain ⟨_,vv,_,sg⟩ := even_weight (p:=p) odd (by omega) ev
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp,vv]; exact sg
  · simp [val_odd od]

end OMA.WeightVal245212

end

section

namespace OMA.EulerSupportUnique245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
open OMA.CofactorEulerSeparation245212
theorem cofactor_divides {h : ℕ} {s : Finset ℕ} (cop : ∀p∈s,h.Coprime p)
    (hit : W h*num s=2*(h*σ 0 h)*den s) : h∣W h := by
  have cp : h.Coprime (num s) := coprime_prod_right_iff.mpr cop
  apply cp.dvd_of_dvd_mul_right
  rw [hit]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _


end OMA.EulerSupportUnique245212

end

section

namespace OMA.RankThreeAnchor245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem dyadic_weight (k : ℕ) : W (2^k)=k*2^(k+1)+1 := by
  rw [w_pow Nat.prime_two]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ _ (k+1),ih,pow_succ (2:ℕ) (k+1)]
    ring

theorem weight_unit {r : ℕ} (pr : r.Prime) (a : ℕ) : r.Coprime (W (r^a)) := by
  apply pr.coprime_iff_not_dvd.mpr
  intro dv
  let : Fact r.Prime := ⟨pr⟩
  have zero := (ZMod.natCast_eq_zero_iff (W (r^a)) r).mpr dv
  rw [w_pow pr,sum_range_succ'] at zero
  push_cast at zero
  simp [pow_succ] at zero


end OMA.RankThreeAnchor245212

end

section

/- A number with exactly one distinct odd prime factor never divides its
own weighted divisor sum. Hence no such cofactor can have an Euler resonance. -/
namespace OMA.SinglePrefixEffective245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.WeightVal245212
open OMA.CofactorEffectiveOriginal245212 OMA.CofactorEulerSeparation245212
open scoped ArithmeticFunction.sigma
open OMA.RankThreeAnchor245212 (weight_unit)
open OMA.RankThreeAnchor245212 (dyadic_weight)

private theorem weight_pos {p a : ℕ} (pr : p.Prime) : 0<W (p^a) := by
  rw [w_pow pr]
  exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨0,Finset.mem_range.mpr (by omega),by simp⟩

private theorem large_power {p k a : ℕ} (hp : 3≤p) (ap : 0<a) (size : 2^(k+1)≤a+2) :
    W (2^k)<p^a := by
  rw [OMA.RankThreeAnchor245212.dyadic_weight]
  cases k with
  | zero =>
    have one:=Nat.pow_le_pow_right (by omega : 0<p) (show 1≤a by omega)
    simp only [pow_one] at one
    omega
  | succ j =>
    cases j with
    | zero =>
      have a2 : 2≤a:=by norm_num at size;omega
      have pw:=(Nat.pow_le_pow_left hp 2).trans (Nat.pow_le_pow_right (by omega : 0<p) a2)
      norm_num at pw ⊢
      omega
    | succ t =>
      let k:=t+2
      have exp (s : ℕ) : 2*((s+2)+1)+2≤2^((s+2)+1) := by
        induction s with
        | zero=>decide
        | succ s ih=>
          calc
            2*(s+1+2+1)+2 ≤ 2*(2*(s+2+1)+2) := by omega
            _ ≤ 2*2^(s+2+1) := Nat.mul_le_mul_left _ ih
            _ = 2^(s+1+2+1) := by rw [show s+1+2+1=(s+2+1)+1 by omega,pow_succ 2 (s+2+1),mul_comm]
      have enough : 2*(k+1)≤a:=by have := exp t;change 2^(t+2+1)≤a+2 at size;dsimp [k];omega
      have power := (Nat.pow_le_pow_right (by decide : 0<2) enough).trans (Nat.pow_le_pow_left (by omega : 2≤p) a)
      apply lt_of_lt_of_le _ power
      change k*2^(k+1)+1<2^(2*(k+1))
      rw [show 2*(k+1)=(k+1)+(k+1) by omega,pow_add 2 (k+1) (k+1)]
      have inc : k+1<2^(k+1):=Nat.lt_two_pow_self
      have gap:=Nat.mul_le_mul_right (2^(k+1)) inc
      have nz:=Nat.two_pow_pos (k+1)
      nlinarith only [gap,nz,inc]

theorem not_divides {k p a : ℕ} (pr : p.Prime) (odd : Odd p) (ap : 0<a) :
    ¬2^k*p^a∣W (2^k*p^a) := by
  have pc:=(Nat.coprime_two_left.mpr odd).pow_left k
  intro hit
  rw [w_mult.map_mul_of_coprime (pc.pow_right a)] at hit
  have pd : p^a∣W (2^k) := ((OMA.RankThreeAnchor245212.weight_unit pr a).pow_left a).dvd_of_dvd_mul_right
    ((dvd_mul_left _ _).trans hit)
  have td : 2^k∣W (p^a) := ((Nat.coprime_two_left.mpr (OMA.DyadicPower245212.dyadic_odd k)).pow_left k).dvd_of_dvd_mul_left
    ((dvd_mul_right _ _).trans hit)
  have order : k≤val (W (p^a)) := (prime_two.pow_dvd_iff_le_factorization (weight_pos pr).ne').mp td
  have localOrder:=weight_local pr odd a
  have size (j : ℕ) (pos : 0<j) (v : k+1≤val j) : 2^(k+1)≤j :=
    Nat.le_of_dvd pos ((pow_dvd_pow 2 v).trans (Nat.ordProj_dvd j 2))
  have big : 2^(k+1)≤a+2 := by
    rcases Nat.even_or_odd (a+1) with ev|od
    · have v:=val_odd (show Odd (a+2) from ev.add_one)
      exact (size (a+1) (by omega) (by omega)).trans (by omega)
    · have v:=val_odd od
      exact size (a+2) (by omega) (by omega)
  have p3 : 3≤p:=by obtain ⟨u,hu⟩:=odd;have := pr.two_le;omega
  exact (large_power p3 ap big).not_ge (Nat.le_of_dvd (by rw [OMA.RankThreeAnchor245212.dyadic_weight];omega) pd)

/-- One whole remaining prime power is bounded even when the cofactor
already contains any prescribed power of a different odd prime. -/
theorem next_atom {k p a m : ℕ} (pr : p.Prime) (odd : Odd p) (ap : 0<a)
    (hm : 1 < m) (cop : (2^k*p^a).Coprime m)
    (eqn : OeisA245212.a (2^k*p^a*m)=(σ 1 (2^k*p^a*m):ℤ)) :
    ∃q∈m.primeFactors,q≤primeHeight (2^k*p^a) m.primeFactors.card ∧
      m.factorization q≤height (2^k*p^a) m.primeFactors.card := by
  apply original (Nat.mul_pos (Nat.two_pow_pos _) (pow_pos pr.pos _)) hm cop _ eqn
  intro t sub eq
  exact not_divides pr odd ap (OMA.EulerSupportUnique245212.cofactor_divides
    (fun q mq=>cop.of_dvd_right (dvd_of_mem_primeFactors (sub mq))) eq)

end OMA.SinglePrefixEffective245212

end

section

namespace OMA.CofactorEffectiveTree245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem support_rest (m p : ℕ) : (ordCompl[p] m).primeFactors=m.primeFactors.erase p := by
  rw [←Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
    Nat.support_factorization]


end OMA.CofactorEffectiveTree245212

end

section

/- Divisibility constraints on a single prime extension. -/
namespace OMA.OddCofactor245212
open Finset ArithmeticFunction OMA.Smooth245212 OMA.Abundance245212
open scoped ArithmeticFunction.sigma

/-- Each new prime divides the sum of the two divisor moments of the remaining cofactor. -/
theorem last_dvd {m p d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p)
    (hd : 0<d) (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) : p∣W m+σ 1 m := by
  have b := balance (mul_ne_zero hm.ne' (pow_ne_zero _ hp.ne_zero)) eq
  have c := cop.pow_right d
  rw [w_mult.map_mul_of_coprime c,isMultiplicative_sigma.map_mul_of_coprime c,
    w_pow hp,sigma_one_apply_prime_pow hp] at b
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have b' := congrArg (fun t : ℕ => (t:ZMod p)) b
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,ZMod.natCast_self] at b' ⊢
  rw [sum_range_succ',sum_range_succ'] at b'
  simp [zero_pow hd.ne',pow_succ] at b'
  exact b'

theorem last_le {m p d : ℕ} (hm : 0 < m) (hp : Nat.Prime p) (cop : m.Coprime p)
    (hd : 0<d) (eq : OeisA245212.a (m*p^d)=(σ 1 (m*p^d):ℤ)) : p≤W m+σ 1 m := by
  apply Nat.le_of_dvd _ (last_dvd hm hp cop hd eq)
  have pos : 0<σ 1 m := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨1,Nat.one_mem_divisors.mpr hm.ne',by decide⟩
  omega

end OMA.OddCofactor245212

end

section

namespace OMA.PairHeight245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open scoped ArithmeticFunction.sigma
theorem last_square {h q f : ℕ} (hh : 0<h) (hq : q.Prime) (qo : q≠2)
    (cop : h.Coprime q) (positive : 0<f)
    (eq : OeisA245212.a (h*q^f)=(σ 1 (h*q^f):ℤ)) : q^f≤(W h+σ 1 h)^2 := by
  let A := W h
  let S := σ 1 h
  have dv := OMA.OddCofactor245212.last_dvd hh hq cop positive eq
  have sp : 0<S := sigma_pos 1 h hh.ne'
  have small : q≤A+S := Nat.le_of_dvd (by omega) dv
  have pow := OMA.PrimePowerDiv245212.cofactor_bound hh hq qo cop f eq
  have bound : ((A:ℤ)-((q:ℤ)-1)*(S:ℤ)).natAbs≤q*(A+S) := by
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]; push_cast
    have q1 : (1:ℤ)≤q := by exact_mod_cast hq.one_le
    apply abs_le.mpr
    constructor <;> nlinarith only [Int.natCast_nonneg A,Int.natCast_nonneg S,
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg A),
      mul_nonneg (sub_nonneg.mpr q1) (Int.natCast_nonneg S)]
  exact (pow.trans bound).trans (by simpa only [sq] using Nat.mul_le_mul_right (A+S) small)

private theorem count_le (h : ℕ) : h.divisors.card≤h := by
  have inc : h.divisors⊆Icc 1 h := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd (Nat.pos_of_ne_zero (mem_divisors.mp hd).2)
      (dvd_of_mem_divisors hd)⟩
  simpa using Finset.card_le_card inc

theorem moment_bound {h : ℕ} (hh : 0<h) : W h+σ 1 h≤2*h^3 := by
  have w : W h≤h^3 := by
    rw [w_apply]
    calc
      _ ≤ ∑ _d∈h.divisors,(h^2 : ℕ) := sum_le_sum fun d hd => by
        have db := Nat.le_of_dvd hh (dvd_of_mem_divisors hd)
        simpa [sq] using Nat.mul_le_mul db ((count_le d).trans db)
      _ ≤ h^3 := by
        simp only [sum_const,nsmul_eq_mul, Nat.cast_id]
        simpa only [show h^3=h*h^2 by ring] using Nat.mul_le_mul_right (h^2) (count_le h)
  have s : σ 1 h≤h^2 := by
    rw [sigma_one_apply]
    calc
      _ ≤ ∑ _d∈h.divisors,h := sum_le_sum fun _ hd => Nat.le_of_dvd hh (dvd_of_mem_divisors hd)
      _ ≤ h^2 := by simpa [sq] using Nat.mul_le_mul_right h (count_le h)
  have h23 : h^2≤h^3 := Nat.pow_le_pow_right hh (by decide)
  omega

theorem combine {h v B : ℕ} (pos : 0<h) (small : h≤B) (large : v≤(W h+σ 1 h)^2) :
    h*v≤4*B^7 := by
  have vBound := large.trans (Nat.pow_le_pow_left (moment_bound pos) 2)
  calc
    _ ≤ h*((2*h^3)^2) := Nat.mul_le_mul_left _ vBound
    _ = 4*h^7 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 7)


end OMA.PairHeight245212

end

section

/- An explicit, unconditional numerical bound on any solution with three
distinct odd prime factors, at each fixed dyadic exponent. -/
namespace OMA.RankThreeEffective245212
open Finset Nat ArithmeticFunction OMA.Smooth245212 OMA.CofactorEffectiveOriginal245212
open scoped ArithmeticFunction.sigma
open OMA.PairHeight245212 (combine)

def stepBound (h r : ℕ) := h*(primeHeight h r+1)^(height h r)
def bound (k : ℕ) :=
  let afterOne:=stepBound (2^k) 3
  let afterTwo:=(range (afterOne+1)).sup (fun h=>stepBound h 2)
  4*afterTwo^7

private theorem step_le {h r p e : ℕ} (pb : p≤primeHeight h r) (eb : e≤height h r) :
    h*p^e ≤ stepBound h r :=
  Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (pb.trans (Nat.le_succ _)) _).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) eb))

theorem original {k m : ℕ} (odd : Odd m) (rank : m.primeFactors.card=3)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : 2^k*m≤bound k := by
  have larger {u : ℕ} (up : 0 < u) (many : 0<u.primeFactors.card) : 1 < u := by
    by_contra! low
    have one : u=1:=by omega
    simp [one] at many
  obtain ⟨p,mp,pb,pa⟩:=dyadic (larger odd.pos (by omega)) odd eqn
  rw [rank] at pb pa
  let a:=m.factorization p
  let h:=2^k*p^a
  let u:=ordCompl[p] m
  have hp:=prime_of_mem_primeFactors mp
  have ap:=hp.factorization_pos_of_dvd odd.pos.ne' (dvd_of_mem_primeFactors mp)
  have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors mp))
  have ou:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (Nat.ordCompl_dvd m p))
  have hc : h.Coprime u :=
    ((Nat.coprime_two_left.mpr ou).pow_left k).mul_left ((Nat.coprime_ordCompl hp odd.pos.ne').pow_left a)
  have ur : u.primeFactors.card=2 := by
    rw [show u.primeFactors=m.primeFactors.erase p from OMA.CofactorEffectiveTree245212.support_rest m p,
      card_erase_of_mem mp,rank]
  have id : h*u=2^k*m := by change 2^k*p^a*u=_; rw [mul_assoc,Nat.ordProj_mul_ordCompl_eq_self]
  have eq1 : OeisA245212.a (h*u)=(σ 1 (h*u):ℤ) := by rwa [id]
  obtain ⟨q,mq,qb,qe⟩:=OMA.SinglePrefixEffective245212.next_atom hp op ap
    (larger ou.pos (by omega : 0<u.primeFactors.card)) hc eq1
  rw [ur] at qb qe
  let b:=u.factorization q
  let v:=ordCompl[q] u
  let g:=h*q^b
  have qq:=prime_of_mem_primeFactors mq
  have ov:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr ou).of_dvd_right (Nat.ordCompl_dvd u q))
  have gc : g.Coprime v :=
    (hc.of_dvd_right (Nat.ordCompl_dvd u q)).mul_left ((Nat.coprime_ordCompl qq ou.pos.ne').pow_left b)
  have gr : v.primeFactors.card=1 := by
    rw [show v.primeFactors=u.primeFactors.erase q from OMA.CofactorEffectiveTree245212.support_rest u q,
      card_erase_of_mem mq,ur]
  have old : g*v=h*u := by change h*q^b*v=_;rw [mul_assoc,Nat.ordProj_mul_ordCompl_eq_self]
  obtain ⟨z,zs⟩:=card_eq_one.mp gr
  have mz : z∈v.primeFactors := by simp [zs]
  have zp:=prime_of_mem_primeFactors mz
  have ez:=zp.factorization_pos_of_dvd ov.pos.ne' (dvd_of_mem_primeFactors mz)
  have nz : z≠2 := by
    intro same
    have dv:=dvd_of_mem_primeFactors mz
    have od:=Nat.odd_iff.mp ov
    rw [same] at dv
    omega
  have rep:=Nat.prod_primeFactors_pow_factorization ov.pos.ne'
  rw [zs,prod_singleton] at rep
  change v=z^(v.factorization z) at rep
  have eq2 : OeisA245212.a (g*z^(v.factorization z))=(σ 1 (g*z^(v.factorization z)):ℤ) := by
    rw [←rep,old];exact eq1
  have gp : 0<g:=Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos k) (pow_pos hp.pos a)) (pow_pos qq.pos b)
  have hb : h ≤ stepBound (2^k) 3 := step_le pb pa
  let L:=stepBound (2^k) 3
  let M:=(range (L+1)).sup (fun j=>stepBound j 2)
  have gb : g≤M := (step_le qb qe).trans (le_sup (f:=fun j=>stepBound j 2) (mem_range.mpr (Nat.lt_succ_of_le hb)))
  have last:=OMA.PairHeight245212.last_square gp zp nz (gc.of_dvd_right (dvd_of_mem_primeFactors mz)) ez eq2
  have fin:=OMA.PairHeight245212.combine gp gb last
  rwa [←rep,old,id] at fin

end OMA.RankThreeEffective245212

end

section

/- Effective whole-integer height whenever two out of three exponent
lengths are within a fixed multiplicative factor of the longest. -/
namespace OMA.TwoTallFinite245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.TwoTallScalar245212
open scoped ArithmeticFunction.sigma Function

def divisorCap (c : ℕ) := (c*minimumCut)^3
def valueCap (c : ℕ) :=
  (∑ j∈range (4*c+1),OMA.RankThreeEffective245212.bound j) +
  ∑ t∈range (divisorCap c+1),2^OMA.DivisorHeight245212.exponentLimit t*OMA.DivisorHeight245212.coreLimit t

theorem bounded {c k m L : ℕ} (p e : Fin 3→ℕ) (hp : ∀i,(p i).Prime) (op : ∀i,Odd (p i)) (inj : p.Injective)
    (he : ∀i,0<e i) (hm : 0 < m) (long : ∀i,i≠2 → m≤e i+1) (cap : ∀i,e i+1≤L)
    (width : L≤c*m)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k*total p e≤valueCap c := by
  classical
  have odd : Odd (total p e) := Nat.coprime_two_left.mp
    (Coprime.prod_right (fun i _ => (Nat.coprime_two_left.mpr (op i)).pow_right _))
  have dvd i : p i∣total p e := (dvd_pow_self _ (he i).ne').trans
    (dvd_prod_of_mem (fun j => p j^e j) (mem_univ i))
  have big : 1<total p e := (hp 0).one_lt.trans_le (Nat.le_of_dvd odd.pos (dvd 0))
  have image : (total p e).primeFactors=univ.image p := by
    ext q
    constructor
    · intro mem
      have pr:=prime_of_mem_primeFactors mem
      obtain ⟨i,_,di⟩:=(pr.prime.dvd_finsetProd_iff _).mp (dvd_of_mem_primeFactors mem :
        q∣∏i,p i^e i)
      exact mem_image.mpr ⟨i,mem_univ _,((prime_dvd_prime_iff_eq pr (hp i)).mp (pr.dvd_of_dvd_pow di)).symm⟩
    · rintro mem
      obtain ⟨i,_,rfl⟩:=mem_image.mp mem
      exact mem_primeFactors.mpr ⟨hp i,dvd i,odd.pos.ne'⟩
  by_cases sk : k≤4*c
  · have rank : (total p e).primeFactors.card=3:=by rw [image,card_image_of_injective _ inj];simp
    have one:=OMA.RankThreeEffective245212.original odd rank eqn
    have sm:=single_le_sum (f:=OMA.RankThreeEffective245212.bound) (fun _ _=>Nat.zero_le _)
      (mem_range.mpr (show k<4*c+1 by omega))
    dsimp only [valueCap];omega
  have kp : 0<k:=by omega
  have small : m≤ minimumCut := by
    by_cases tiny : m≤4
    · exact tiny.trans (by decide)
    have comp : 4*max k L < k*m := by
      rw [mul_max_of_nonneg _ _ (by decide : (0:ℕ)≤4)]
      apply max_lt
      · calc
          4*k=k*4:=by ring
          _ < k*m:=Nat.mul_lt_mul_of_pos_left (by omega) kp
      · calc
          4*L ≤ 4*(c*m):=Nat.mul_le_mul_left _ width
          _ = (4*c)*m:=by ring
          _ < k*m:=Nat.mul_lt_mul_of_pos_right (by omega) hm
    exact (OMA.TwoTallOriginal245212.shortest p e hp op inj he kp hm long cap comp eqn).le
  have pair : (↑(univ : Finset (Fin 3)) : Set (Fin 3)).Pairwise
      (Nat.Coprime on (fun i => p i^e i)) := by
    intro i _ j _ ne
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (inj.ne ne)).pow_left _).pow_right _
  have count : (total p e).divisors.card=∏i,(e i+1) := by
    rw [←sigma_zero_apply]
    simpa [total,sigma_zero_apply_prime_pow (hp _)] using
      IsMultiplicative.map_prod (fun i => p i^e i) (isMultiplicative_sigma (k:=0)) univ pair
  have lc : L≤c*minimumCut:=width.trans (Nat.mul_le_mul_left _ small)
  have tc : (total p e).divisors.card≤divisorCap c := by
    rw [count]
    calc
      _ ≤ ∏_i : Fin 3,c*minimumCut := prod_le_prod' (fun i _=>(cap i).trans lc)
      _ = _ := by simp [divisorCap]
  have ⟨ke,co⟩:=OMA.DivisorHeight245212.effective_box odd big eqn
  have h:= (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) ke.le) co).trans
    (single_le_sum (f:=fun t=>2^OMA.DivisorHeight245212.exponentLimit t*OMA.DivisorHeight245212.coreLimit t)
      (fun _ _=>Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le tc)))
  exact h.trans (Nat.le_add_left _ _)

end OMA.TwoTallFinite245212

end

section

/- In particular the largest prime can carry the largest exponent only
finitely often. The exponents at the two smaller primes cannot be
linearly comparable in an infinite family either. -/
namespace OMA.TwoTallConsequences245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.TwoTallFinite245212
open scoped ArithmeticFunction.sigma

theorem from_order {C k p q r a b d m L : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (op : Odd p) (oq : Odd q) (or' : Odd r) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (ap : 0<a) (bp : 0<b) (dp : 0<d) (hm : 0 < m) (lo : m≤a+1 ∧ m≤b+1)
    (hi : a+1≤L ∧ b+1≤L ∧ d+1≤L) (width : L≤C*m)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    2^k*p^a*q^b*r^d ≤ valueCap C := by
  let P : Fin 3→ℕ:=![p,q,r]
  let E : Fin 3→ℕ:=![a,b,d]
  have prime (i) : (P i).Prime:=by fin_cases i <;> simp [P,pp,qp,rp]
  have odd (i) : Odd (P i):=by fin_cases i <;> simp [P,op,oq,or']
  have inj : P.Injective:=by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [P]
  have pos (i):0<E i:=by fin_cases i <;> simpa [E] using (show 0<_ by first | exact ap | exact bp | exact dp)
  have lon (i) (ne:i≠2) : m≤E i+1:=by fin_cases i <;> simp [E] at * <;> omega
  have cap (i):E i+1≤L := by fin_cases i <;> simp [E] <;> omega
  have repr : 2^k*total P E=2^k*p^a*q^b*r^d := by simp [total,Fin.prod_univ_three,P,E,mul_assoc]
  have result:=bounded P E prime odd inj pos hm lon cap width (by rw [repr];exact eqn)
  rwa [repr] at result

theorem lower_comparable {C k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p3 : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (width : max (a+1) (b+1) ≤ C*min (a+1) (b+1))
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    2^k*p^a*q^b*r^d ≤ valueCap (20*C) := by
  have ld:=OMA.LargeLastOriginal245212.largest pp qp rp p3 pq qr ap bp dp eqn
  let t:=max (a+1) (b+1)
  apply from_order pp qp rp (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega))
    (rp.odd_of_ne_two (by omega)) pq.ne (pq.trans qr).ne qr.ne ap bp dp
    (m:=min (a+1) (b+1)) (L:=20*t) (by omega) ⟨min_le_left ..,min_le_right ..⟩
    (by dsimp [t];omega) _ eqn
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 20 width

theorem largest_at_largest {k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p3 : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (big : max a b≤d)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    2^k*p^a*q^b*r^d ≤ valueCap 20 := by
  have ld:=OMA.LargeLastOriginal245212.largest pp qp rp p3 pq qr ap bp dp eqn
  have op:=pp.odd_of_ne_two (by omega)
  have oq:=qp.odd_of_ne_two (by omega)
  have or':=rp.odd_of_ne_two (by omega)
  by_cases ab : a≤b
  · have out:=from_order (C:=20) (k:=k) (a:=b) (b:=d) (d:=a) qp rp pp oq or' op qr.ne pq.ne.symm
      (pq.trans qr).ne.symm bp dp ap (m:=b+1) (L:=d+1) (by omega) (by omega) (by omega)
      (by omega) (by simpa only [mul_comm,mul_assoc,mul_left_comm] using eqn)
    simpa only [mul_comm,mul_assoc,mul_left_comm] using out
  · have out:=from_order (C:=20) (k:=k) (a:=a) (b:=d) (d:=b) pp rp qp op or' oq (pq.trans qr).ne
      pq.ne qr.ne.symm ap dp bp (m:=a+1) (L:=d+1) (by omega) (by omega) (by omega)
      (by omega) (by simpa only [mul_comm,mul_assoc,mul_left_comm] using eqn)
    simpa only [mul_comm,mul_assoc,mul_left_comm] using out

end OMA.TwoTallConsequences245212

end





/- The dyadic prime power is polynomial in the largest odd exponent -/

section

/- Cleared moments and the restriction on every retained prime. -/
namespace OMA.SingleMovingGap245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212

structure Family where
  p : Fin 3→ℕ
  e : Fin 3→ℕ
  k : ℕ
  L : ℕ
  prime : ∀i,(p i).Prime
  positive : ∀i,0<e i
  kp : 8≤k
  longest : ∃i,e i+1=L
  cap : ∀i,e i+1≤L
  inj : p.Injective

def exactX (c : Family) (i : Fin 3) := X (c.p i) (some (c.e i))
def exactY (c : Family) (i : Fin 3) := Y (c.p i) (some (c.e i))
def x' (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) := xx' (c.p i) (c.e i) (b i)
def y' (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) := yy' (c.p i) (c.e i) (b i)
def dust (c : Family) (b : Fin 3→Option Bool) := ∏i,Dn (c.p i) (c.e i) (b i)
def NX (c : Family) (b : Fin 3→Option Bool) := ∏i,Nx (c.p i) (c.e i) (b i)
def NY (c : Family) (b : Fin 3→Option Bool) := ∏i,Ny (c.p i) (c.e i) (b i)
def score (f g : ℕ) (x y : Fin 3→ℚ) := (f:ℚ)*(∏i,x i)+(g:ℚ)*(∏i,y i)

theorem dust_pos (c : Family) (b : Fin 3→Option Bool) : 0<dust c b :=
  prod_pos (fun i _=>Dpos (c.prime i) _ _)

theorem clear (c : Family) (b : Fin 3→Option Bool) (f g : ℕ) :
    score f g (x' c b) (y' c b)*dust c b=(f*NX c b+g*NY c b:ℕ) := by
  have w : (∏i,x' c b i)*(dust c b:ℚ)=NX c b := by
    dsimp [dust,NX,x'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).1)
  have s : (∏i,y' c b i)*(dust c b:ℚ)=NY c b := by
    dsimp [dust,NY,y'];push_cast;rw [←prod_mul_distrib]
    exact prod_congr rfl (fun i _=>(moments (c.prime i) (c.e i) (b i)).2)
  dsimp [score];push_cast
  linear_combination (f:ℚ)*w+(g:ℚ)*s


private theorem largest {c : Family} {b : Fin 3→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := by
  classical
  let s:=univ.filter (fun j=>b j=some true)
  intro i hi
  have im : i∈s:=mem_filter.mpr ⟨mem_univ _,hi⟩
  obtain ⟨j,jm,top⟩:=s.exists_max_image c.p ⟨i,im⟩
  have sh: b j=some true := (mem_filter.mp jm).2
  let q:=c.p j
  have pr:=c.prime j
  have dn : q∣NX c b := by
    apply dvd_trans (b:=Nx (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Nx (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Nx,OMA.ThreeMovingLocal245212.xn,sh,q]
  have ds : q∣NY c b := by
    apply dvd_trans (b:=Ny (c.p j) (c.e j) (b j)) _ (dvd_prod_of_mem (fun i=>Ny (c.p i) (c.e i) (b i)) (mem_univ j))
    simp [Ny,OMA.ThreeMovingLocal245212.yn,sh,q]
  have total : q∣(f+g)*dust c b := hit ▸ dvd_add (dvd_mul_of_dvd_right dn f) (dvd_mul_of_dvd_right ds g)
  apply (top _ im).trans
  by_contra! no
  change max (c.k+1) c.L < q at no
  rw [frac] at total
  rcases pr.dvd_mul.mp total with h|h
  · rcases pr.dvd_mul.mp h with small|bad
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) small
    · exact unit j bad
  · obtain ⟨i',_,v⟩:=(pr.prime.dvd_finsetProd_iff _).mp h
    have le0:=c.cap i'
    have absent := Nat.not_dvd_of_pos_of_lt (by omega : 0<c.e i'+1) (by omega : c.e i'+1<q)
    change q∣Dn (c.p i') (c.e i') (b i') at v
    cases which : b i' with
    | none =>
      rw [which] at v
      rcases pr.dvd_mul.mp v with hit|hit
      · exact absent hit
      have same:=c.inj ((prime_dvd_prime_iff_eq pr (c.prime i')).mp (pr.dvd_of_dvd_pow hit))
      exact (by rw [←same,sh] at which; contradiction)
    | some bit =>
      cases bit with
      | false => rw [which] at v;exact absent v
      | true =>
        have mt : i'∈s:=mem_filter.mpr ⟨mem_univ _,which⟩
        have sz:=top i' mt
        rw [which] at v
        rcases pr.dvd_mul.mp v with bad|bad
        · exact absent bad
        · exact Nat.not_dvd_of_pos_of_lt (by have:=(c.prime i').two_le;omega : 0<c.p i'-1)
            (by omega) (pr.dvd_of_dvd_pow bad)


theorem retained {c : Family} {b : Fin 3→Option Bool} {f g l : ℕ} (frac : f+g=(c.k+1)*l)
    (unit : ∀i,¬c.p i∣l) (hit : (f+g)*dust c b=f*NX c b+g*NY c b) :
    ∀i,b i=some true → c.p i≤ max (c.k+1) c.L := largest frac unit hit

end OMA.SingleMovingGap245212

end

section

/- A negative contribution when a retained coordinate returns to its true
moment is dominated by the deficit of the dyadic linearization. -/
namespace OMA.SingleMovingLoss245212
open Nat Finset OMA.Smooth245212 OMA.TwoTallLocal245212 OMA.SingleMovingGap245212
open OMA.ThreeMovingLocal245212 (xx yy)
open OMA.ThreeMovingLocal245212 (quotients)
open OMA.DyadicLeast245212 (x_two_terms)

theorem single_lb {p e : ℕ} (hp : p.Prime) (he : 0<e) :
    1≤(2*(p:ℚ))*(X p (some e)-1) := by
  have r:=OMA.DyadicLeast245212.x_two_terms hp he
  change 1+(e:ℚ)/((e+1)*p)≤_ at r
  have z : 0<((e:ℚ)+1)*p := by have:=hp.pos;positivity
  have z' := (div_le_iff₀ z).mp (by linarith only [r] : (e:ℚ)/((e+1)*p)≤X p (some e)-1)
  have q : (1:ℚ)≤e:=by exact_mod_cast he
  by_contra! bad
  have mul:=mul_lt_mul_of_pos_right bad (by positivity : 0<(e:ℚ)+1)
  nlinarith only [z',q,mul]

theorem scalar {k p e : ℕ} (hk : 8≤k) (kp : k+1<p) (len : p≤e+1) :
    8*p*(2^(k+1)-1)≤p^e := by
  have k4 : 4≤k:=by omega
  have c : 16≤2^k := (by decide : 16≤2^4).trans (Nat.pow_le_pow_right (by decide) k4)
  have ep : k+1≤e:=by omega
  calc
    _ ≤ 8*p*(2^(k+1)) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = p*(2^k*16) := by rw [pow_succ];ring
    _ ≤ p*(2^k*2^k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c)
    _ = p*(2*2)^k := by rw [mul_pow]
    _ ≤ p*p^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = p^(k+1) := (pow_succ' ..).symm
    _ ≤ p^e := Nat.pow_le_pow_right (by omega) ep

/-- Returns a coordinate from any of the three proxy choices. The comparison
tests u*y*y' against k, keeping the product of the *other* ordinary factors. -/
theorem restore {p e k : ℕ} (hp : p.Prime) (ep : 0<e) (kp : 0<k) (mode : Option Bool)
    (x x' y y' allowance : ℚ) (xp : 1≤x) (xp' : 1≤x') (yp : 0≤y) (yp' : 0≤y')
    (yl : y*y'≤1) (dl : 0≤allowance)
    (bad : mode=some true → (k:ℚ)<((p:ℚ)-1)*(y*y') → 1/(p:ℚ)^e≤allowance) :
    (k:ℚ)*xx' p e mode*x*x'+yy' p e mode*y*y' ≤
    (k:ℚ)*X p (some e)*x*x'+Y p (some e)*y*y'+allowance := by
  cases mode with
  | none=> dsimp [xx',yy'];linarith
  | some t=>
    cases t with
    | false=>
      have v:=OMA.TwoTallLocal245212.move hp ep (by decide : 0 < (1:ℕ)) kp (by decide : 0<(1:ℕ))
        (le_refl (k*1)) false (by simp) x x' y y' xp xp' yp yp' (by norm_num;linarith)
      dsimp [xx',yy'];push_cast at v;linarith only [v,dl]
    | true=>
      let u:ℚ:=(p:ℚ)-1
      let H:ℚ:=(e:ℚ)+1
      let d:ℚ:=1/(H*u^2*(p:ℚ)^e)
      have u1 : 1≤u:=by dsimp [u];have z:=(by exact_mod_cast hp.two_le : (2:ℚ)≤p);linarith
      have h1 : 1≤H:=by dsimp [H];have z:=Nat.cast_nonneg (α:=ℚ) e;linarith
      have po : (0:ℚ)<(p:ℚ)^e:=pow_pos (by exact_mod_cast hp.pos) _
      have dpos : 0<d:=by dsimp [d];positivity
      have vk : 0≤(k:ℚ)*(x*x'):=mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
      have xy : 1≤x*x':=one_le_mul_of_one_le_of_one_le xp xp'
      have m:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
      change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at m
      change _*xx p e true*x*x'+yy p e true*y*y'≤_
      rw [m.1,m.2]
      by_cases good : u*(y*y')≤k
      · have more:=(mul_le_mul_of_nonneg_left xy (Nat.cast_nonneg (α:=ℚ) k))
        have dif : 0≤(k:ℚ)*x*x'-u*(y*y'):=by linarith [good,more]
        nlinarith only [mul_nonneg dpos.le dif,dl]
      · have limit:=bad rfl (lt_of_not_ge good)
        have ud : u*d=1/((H*u)*(p:ℚ)^e) := by dsimp [d];field_simp
        have abd : u*d≤1/(p:ℚ)^e := by
          rw [ud]
          exact one_div_le_one_div_of_le po (le_mul_of_one_le_left po.le (one_le_mul_of_one_le_of_one_le h1 u1))
        have loss:=mul_le_mul_of_nonneg_left yl (mul_nonneg (by linarith : 0≤u) dpos.le)
        nlinarith only [loss,abd,limit,mul_nonneg dpos.le vk]

end OMA.SingleMovingLoss245212

end

section

/- The actual dyadic deficit exceeds the total possible loss caused by
all risky rounded coordinates, without any comparability assumption. -/
namespace OMA.SingleMovingProxy245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingOriginal245212 (G)
def deficit (c : Family) : ℚ := (c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c)

theorem lower (c : Family) (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) (i) :
    1≤(2*(c.p i:ℚ))*(G c.k)*(deficit c) := by
  have xb j : 1≤exactX c j:=(ranges (c.prime j) (c.positive j) none).1
  have xi : exactX c i≤∏j,exactX c j := by
    rw [←prod_erase_mul (univ : Finset (Fin 3)) (exactX c) (mem_univ i)]
    exact le_mul_of_one_le_left (zero_le_one.trans (xb _)) (one_le_prod (fun j _=>xb j))
  have localBound:=OMA.SingleMovingLoss245212.single_lb (c.prime i) (c.positive i)
  change 1≤(2*(c.p i:ℚ))*(exactX c i-1) at localBound
  have xm : 0≤(∏j,exactX c j)-1:=by linarith only [xi,xb i]
  have more:=mul_nonneg (Nat.cast_nonneg (α:=ℚ) c.k) xm
  have cc : 0≤2*(c.p i:ℚ):=by positivity
  nlinarith only [localBound,mul_le_mul_of_nonneg_left xi cc,mul_nonneg cc more,
    congrArg (fun z:ℚ=>2*(c.p i:ℚ)*z) link]

theorem positive (c : Family) (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) : 0<deficit c := by
  have h:=lower c link 0
  by_contra! n
  have t:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(c.p 0:ℚ)*(G c.k:ℕ) by positivity) n
  linarith

theorem separated (c : Family) (b : Fin 3→Option Bool)
    (link : deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1)) :
    (c.k+1)*dust c b ≠ c.k*NX c b+NY c b := by
  intro hit
  have gd : 0<deficit c:=positive c link
  have scale:=retained (b:=b) (f:=c.k) (g:=1) (l:=1) (by simp)
    (fun i=>Nat.not_dvd_of_pos_of_lt (by decide) (c.prime i).one_lt) (by simpa using hit)
  let mix (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactY c i else y' c b i
  have adv (s : Finset (Fin 3)) {i} (fresh : i∉s) :
      score c.k 1 (mix s) (miy s)≤ score c.k 1 (mix (insert i s)) (miy (insert i s))+deficit c/4 := by
    have bound j : 1≤ mix s j ∧ 0≤ miy s j ∧ miy s j≤2/((c.e j:ℚ)+1) := by
      by_cases mem : j∈s
      · have v:=ranges (c.prime j) (c.positive j) none
        simpa only [mix,miy,if_pos mem,exactX,exactY,xx',yy'] using And.intro v.1 v.2.2
      · have v:=ranges (c.prime j) (c.positive j) (b j)
        simpa only [mix,miy,if_neg mem,x',y'] using And.intro v.1 v.2.2
    have size j : miy s j≤1:= (bound j).2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
      have:= (by exact_mod_cast c.positive j : (1:ℚ)≤c.e j);linarith))
    have single {j l : Fin 3} (n : j≠i) (n' : l≠i) (jl : j≠l) :
        (c.k:ℚ)*mix s i*mix s j*mix s l+miy s i*miy s j*miy s l ≤
        c.k*mix (insert i s) i*mix (insert i s) j*mix (insert i s) l+
          miy (insert i s) i*miy (insert i s) j*miy (insert i s) l+deficit c/4 := by
      have prod : miy s j*miy s l≤1:=mul_le_one₀ (size j) (bound l).2.1 (size l)
      have step:=OMA.SingleMovingLoss245212.restore (c.prime i) (c.positive i) (by have:=c.kp;omega : 0<c.k)
        (b i) (mix s j) (mix s l) (miy s j) (miy s l) (deficit c/4)
        (bound j).1 (bound l).1 (bound j).2.1 (bound l).2.1 prod (by positivity)
      suffices bad : b i=some true → (c.k:ℚ)<((c.p i:ℚ)-1)*(miy s j*miy s l) →
          1/(c.p i:ℚ)^(c.e i)≤deficit c/4 by
        simpa [mix,miy,exactX,exactY,x',y',fresh,n,n'] using step bad
      intro bit risk
      have pk : c.k+1<c.p i := by
        have h:=mul_le_mul_of_nonneg_left prod (show (0:ℚ)≤(c.p i:ℚ)-1 by have:= (by exact_mod_cast (c.prime i).one_le : (1:ℚ)≤c.p i);linarith)
        exact_mod_cast (show (c.k:ℚ)+1<c.p i by linarith only [h,risk])
      have pL : c.p i≤c.L:=by have:=scale i bit;omega
      have excluded (z z' : Fin 3) (prod' : miy s j*miy s l=miy s z*miy s z') (maximal : c.e z+1=c.L) : False := by
        have up:=mul_le_mul_of_nonneg_left (size z') (bound z).2.1
        have Y:= (le_div_iff₀ (by positivity)).mp (bound z).2.2
        have PL : (c.p i:ℚ)-1≤(c.e z:ℚ)+1:=by
          have hh : c.p i≤c.e z+1:=by omega
          have v : (c.p i:ℚ)≤c.e z+1:=by exact_mod_cast hh
          linarith
        have cp:=mul_nonneg (bound z).2.1 (bound z').2.1
        have t1:=mul_le_mul_of_nonneg_right PL cp
        have t2:=mul_le_mul_of_nonneg_right up (show (0:ℚ)≤(c.e z:ℚ)+1 by positivity)
        rw [prod'] at risk
        have k8 : (8:ℚ)≤c.k:=by exact_mod_cast c.kp
        nlinarith only [risk,Y,t1,t2,k8]
      obtain ⟨v,vbig⟩:=c.longest
      have caseV : v=i ∨ v=j ∨ v=l:=by omega
      have len : c.p i≤c.e i+1 := by
        rcases caseV with rfl|rfl|rfl
        · omega
        · exact False.elim (excluded _ _ rfl vbig)
        · exact False.elim (excluded _ _ (mul_comm _ _) vbig)
      have pw:=OMA.SingleMovingLoss245212.scalar c.kp pk len
      have more:=lower c link i
      have pwq : 8*(c.p i:ℚ)*(G c.k)≤(c.p i:ℚ)^(c.e i):=by exact_mod_cast pw
      apply (div_le_iff₀ (by have:=(c.prime i).pos;positivity : (0:ℚ)<(c.p i:ℚ)^(c.e i))).mpr
      nlinarith only [more,mul_le_mul_of_nonneg_right pwq gd.le]
    dsimp [score];simp only [Fin.prod_univ_three,one_mul]
    have choice : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choice with rfl|rfl|rfl
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=1) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=1) (by decide) (by decide) (by decide)
  have a:=adv ∅ (i:=0) (by decide)
  have b1:=adv {0} (i:=1) (by decide)
  have d:=adv {1,0} (i:=2) (by decide)
  have un : insert (2:Fin 3) ({1,0}:Finset (Fin 3))=univ:=by decide
  rw [un] at d
  have a' : score c.k 1 (x' c b) (y' c b)≤ score c.k 1 (mix {0}) (miy {0})+deficit c/4:=by simpa only [mix,miy,notMem_empty,if_false,Finset.insert_empty] using a
  have d' : score c.k 1 (mix {1,0}) (miy {1,0}) ≤ score c.k 1 (exactX c) (exactY c)+deficit c/4:=by simpa only [mix,miy,mem_univ,if_true] using d
  have eq:=clear c b c.k 1
  simp only [one_mul] at eq
  rw [←hit] at eq
  push_cast at eq
  have dp : (0:ℚ)<dust c b:=by exact_mod_cast dust_pos c b
  have eq' : score c.k 1 (x' c b) (y' c b)=(c.k:ℚ)+1:=mul_right_cancel₀ dp.ne' eq
  dsimp only [deficit] at a' b1 d' gd
  linarith only [a',b1,d',eq',gd]

end OMA.SingleMovingProxy245212

end

section

/- A missing interval among six local scales makes the local tail
smaller than a nonzero integer's reciprocal denominator. -/
namespace OMA.SingleMovingStep245212
open Nat Finset OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212 OMA.SingleMovingGap245212
open OMA.TwoTallScalar245212 (cut cut_mono cut_succ)
open OMA.CofactorEffectiveAtom245212 (product_error)

theorem empty_six (x : ℕ) (hx : 1≤x) (p : Fin 6→ℕ) :
    ∃j : Fin 7,∀i, p i ≤ cut x j.val ∨ cut x (j.val+1) < p i := by
  by_contra! no
  choose f above below using no
  have inj:Function.Injective f := by
    intro j k eqn
    rcases lt_trichotomy j k with lt|eq|gt
    · have h := cut_mono hx (show j.val+1≤k.val from lt)
      have impossible:=(below j).trans h
      rw [eqn] at impossible
      exact False.elim ((above k).not_ge impossible)
    · exact eq
    · have h := cut_mono hx (show k.val+1≤j.val from gt)
      have impossible:=(below k).trans h
      rw [←eqn] at impossible
      exact False.elim ((above j).not_ge impossible)
  have:=Fintype.card_le_of_injective _ inj
  norm_num at this

def degree : ℕ := 16^7

theorem integer_gap (c : Family) (bits : Fin 3→Option Bool) (f g : ℕ)
    (different : (f+g)*dust c bits ≠ f*NX c bits+g*NY c bits) :
    (1:ℚ)≤|score f g (x' c bits) (y' c bits)-(f+g:ℕ)| * dust c bits := by
  let B:=dust c bits
  let T:=f*NX c bits+g*NY c bits
  let L:ℤ:=(T:ℤ)-((f+g)*B:ℕ)
  have nz : L≠0 := fun h => different (by exact_mod_cast (sub_eq_zero.mp h).symm)
  have la : (1:ℤ)≤|L| := by have:=abs_pos.mpr nz;omega
  have raw : (1:ℚ)≤|(T:ℚ)-((f+g)*B:ℕ)| := by dsimp [L] at la;exact_mod_cast la
  have ab:=congrArg (fun w:ℚ=>|w|) (show (score f g (x' c bits) (y' c bits)-(f+g:ℕ))*B =
      (T:ℚ)-((f+g)*B:ℕ) by rw [sub_mul];push_cast;rw [show score f g (x' c bits) (y' c bits)*B=(T:ℚ) from clear ..])
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg B : (0:ℚ)≤B)] at ab
  exact ab.trans_ge raw

theorem difference (c : Family) (b : Fin 3→Option Bool) (f g N : ℕ) (n0 : 0<N)
    (space : ∀ i t, b i=some t → N ≤ (if t then (c.p i)^(c.e i) else c.p i)) :
    |score f g (x' c b) (y' c b)-score f g (exactX c) (exactY c)|≤48*((f:ℚ)+g)/N := by
  have bp i := ranges (c.prime i) (c.positive i) (b i)
  have ex i := ranges (c.prime i) (c.positive i) none
  have er (i) : |exactX c i-x' c b i|≤2/(N:ℚ) ∧ |exactY c i-y' c b i|≤2/(N:ℚ) := by
    cases h:b i with
    | none=>simp [exactX,x',exactY,y',h,xx',yy'];positivity
    | some t=>simpa [exactX,x',exactY,y',h,xx',yy'] using error (c.prime i) (c.positive i) n0 t (space i t h)
  have eps : (0:ℚ)≤2/N := by positivity
  have one i : 2/((c.e i:ℚ)+1)≤2 := div_le_self (by decide) (by have:=Nat.cast_nonneg (α:=ℚ) (c.e i);linarith)
  have x:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactX c) (x' c b) eps
    (fun i _=>⟨zero_le_one.trans (ex i).1,(ex i).2.1,zero_le_one.trans (bp i).1,(bp i).2.1,(er i).1⟩)
  have y:=OMA.CofactorEffectiveAtom245212.product_error (univ:Finset (Fin 3)) (exactY c) (y' c b) eps
    (fun i _=>⟨(ex i).2.2.1,(ex i).2.2.2.trans (one i),(bp i).2.2.1,(bp i).2.2.2.trans (one i),(er i).2⟩)
  norm_num at x y
  dsimp [score]
  rw [abs_sub_comm]
  calc
    _ = |(f:ℚ)*((∏i,exactX c i)-∏i,x' c b i)+(g:ℚ)*((∏i,exactY c i)-∏i,y' c b i)| := by congr 1;ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg f : (0:ℚ)≤f),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg g : (0:ℚ)≤g)]
      simp only [div_eq_mul_inv] at x y ⊢
      nlinarith only [mul_le_mul_of_nonneg_left x (Nat.cast_nonneg f : (0:ℚ)≤f),
        mul_le_mul_of_nonneg_left y (Nat.cast_nonneg g : (0:ℚ)≤g)])

theorem contradiction (c : Family) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (separated : ∀ b, (f+g)*dust c b ≠ f*NX c b+g*NY c b)
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^degree:ℕ):ℚ)) : False := by
  let point : Fin 6 → ℕ := ![c.p 0,c.p 1,c.p 2,c.p 0^c.e 0,c.p 1^c.e 1,c.p 2^c.e 2]
  obtain ⟨j,band⟩:=empty_six x (by omega) point
  have bp (i:Fin 3) : c.p i≤cut x j.val ∨ cut x (j.val+1)<c.p i := by
    fin_cases i <;> first | exact band 0 | exact band 1 | exact band 2
  have bd (i:Fin 3) : c.p i^c.e i≤cut x j.val ∨ cut x (j.val+1)<c.p i^c.e i := by
    fin_cases i <;> first | exact band 3 | exact band 4 | exact band 5
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^degree:=cut_mono (by omega) (show j.val+1≤7 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simpa [lo] using ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^9 := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have nz:=separated b
  have iga:=integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega

end OMA.SingleMovingStep245212

end

section

/- The dyadic factor of every solution with three distinct odd primes
is polynomially bounded in the largest odd exponent length. -/
namespace OMA.SingleMovingOriginal245212
open Nat Finset ArithmeticFunction OMA.SingleMovingGap245212 OMA.SingleMovingStep245212
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.TwoTallScalar245212 (base)
open OMA.Smooth245212 (total W)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)
theorem identities (k : ℕ) : 0<G k ∧ F k+G k=(k+1)*2^(k+1) ∧ F k=k*G k+(k+1) := by
  have g:=Nat.two_pow_pos k
  dsimp [F,G];rw [pow_succ]
  have sub:=Nat.sub_add_cancel (show 1≤2^k*2 by omega)
  exact ⟨by omega,by nlinarith only [sub],by nlinarith only [congrArg (k*·) sub]⟩


theorem physical (c : Family) (k : ℕ) (op : ∀i,Odd (c.p i)) (inj : c.p.Injective)
    (eqn : OeisA245212.a (2^k*total c.p c.e)=(σ 1 (2^k*total c.p c.e):ℤ)) :
    score (F k) (G k) (exactX c) (exactY c)=(F k+G k:ℕ) := by
  let t:=2^k*σ 0 (2^k)
  have t0 : 0<t := Nat.mul_pos (Nat.two_pow_pos k) (sigma_pos 0 _ (Nat.two_pow_pos k).ne')
  have norm:=OMA.CofactorCrossOriginal245212.normalized_extension (p:=c.p) (e:=c.e) (Nat.two_pow_pos k)
    c.prime inj (fun i=>(Nat.coprime_two_left.mpr (op i)).pow_left k) eqn
  change ((W (2^k):ℚ)/t)*(∏i,exactX c i)+((σ 1 (2^k):ℚ)/t)*(∏i,exactY c i)=2 at norm
  field_simp [show (t:ℚ)≠0 by exact_mod_cast t0.ne'] at norm
  have z0:=Nat.two_pow_pos (k+1)
  have gold : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from z0)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have fold : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  have ht : 2*t=F k+G k := by
    dsimp [t];rw [sigma_zero_apply_prime_pow Nat.prime_two,(identities k).2.1,pow_succ];ring
  rw [gold,fold] at norm
  dsimp [score];rw [←ht];push_cast;linarith only [norm]


theorem coarse (c : Family) (op : ∀i,Odd (c.p i))
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    G c.k < 8*(c.k+1)*(base c.k c.L)^degree := by
  have exact:=physical c c.k op c.inj eqn
  let x:=base c.k c.L
  have big : 128≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cf : c.k+1≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have cl : c.L≤x := by dsimp [base,x];nlinarith only [Nat.zero_le (c.k*c.L),Nat.zero_le c.k,Nat.zero_le c.L]
  have dx : 1≤x:=by omega
  have r0 := (identities c.k).1
  let PX:=∏i,exactX c i
  let PY:=∏i,exactY c i
  have xb i := OMA.TwoTallLocal245212.ranges (c.prime i) (c.positive i) none
  have low : (1:ℚ)≤PX:=one_le_prod (fun i _=>(xb i).1)
  have top : PX≤8 := calc
    _ ≤ ∏_i:Fin 3,(2:ℚ) := prod_le_prod (fun i _=>zero_le_one.trans (xb i).1) (fun i _=>(xb i).2.1)
    _ = _ := by norm_num
  have id : (G c.k:ℚ)*((c.k:ℚ)+1-score c.k 1 (exactX c) (exactY c))=((c.k:ℚ)+1)*(PX-1) := by
    change (F c.k:ℚ)*PX+(G c.k:ℚ)*PY=(F c.k+G c.k:ℕ) at exact
    change _*((c.k:ℚ)+1-((c.k:ℚ)*PX+(1:ℕ)*PY))=_
    have f : (F c.k:ℚ)=(c.k:ℚ)*G c.k+(c.k+1:ℕ) := by exact_mod_cast (identities c.k).2.2
    push_cast at f exact ⊢
    linear_combination -exact+(PX-1)*f
  have gp : (0:ℚ)<G c.k := by exact_mod_cast r0
  by_contra! ample
  have below : score c.k 1 (exactX c) (exactY c)≤(c.k+1:ℕ):=by
    push_cast
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (id ▸ mul_nonneg (by positivity) (sub_nonneg.mpr low)) gp)
  have close : |score c.k 1 (exactX c) (exactY c)-(c.k+1:ℕ)|≤1/((x^degree:ℕ):ℚ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr below),neg_sub]
    have h : (((c.k+1:ℕ):ℚ)-score c.k 1 (exactX c) (exactY c))*(x^degree:ℕ)≤1 := by
      apply le_of_mul_le_mul_left (a:=(G c.k:ℚ)) _ gp
      have g0 : (8:ℚ)*(c.k+1)*(x^degree:ℕ)≤G c.k:=by exact_mod_cast ample
      push_cast at g0 ⊢
      nlinarith only [congrArg (·*(x:ℚ)^degree) id,g0,
        mul_le_mul_of_nonneg_right (show PX-1≤8 by linarith) (show 0≤((c.k:ℚ)+1)*x^degree by positivity)]
    exact (le_div_iff₀ (by exact_mod_cast pow_pos dx degree : (0:ℚ)<(x^degree:ℕ))).mpr h

  apply OMA.SingleMovingStep245212.contradiction c c.k 1 x big cf cl _ close
  intro b
  have link : OMA.SingleMovingProxy245212.deficit c*(G c.k:ℕ)=((c.k:ℚ)+1)*((∏i,exactX c i)-1) := by
    simpa only [OMA.SingleMovingProxy245212.deficit,mul_comm] using id
  simpa only [one_mul] using OMA.SingleMovingProxy245212.separated c b link

end OMA.SingleMovingOriginal245212

end

section

/- Explicit polynomial control on the dyadic prime power in terms of
the largest odd exponent length alone. -/
namespace OMA.SingleMovingHeight245212
open Nat Finset ArithmeticFunction
open OMA.ThreeMovingOriginal245212 (G)
open OMA.TwoTallScalar245212 (base)
open OMA.SingleMovingStep245212 (degree)
open OMA.SingleMovingGap245212 (Family)
open OMA.Smooth245212 (total)
open scoped ArithmeticFunction.sigma

def constant (D : ℕ) := 2^(16*(D+2)^2+8)+(16*128^D)^2

private theorem eliminate {k L D : ℕ}
    (h : 2^k ≤ 8*(k+1)*(base k L)^D) :
    2^k ≤ constant D*(L+1)^(2*D) := by
  have pos : 1≤(L+1)^(2*D):=Nat.one_le_pow _ _ (by omega)
  by_cases large : 16*(D+2)^2≤k+2
  · have grow:=OMA.ComplementarySize245212.absorb (b:=k+2) (d:=D+1) (by simpa [Nat.add_assoc] using large)
    let C : ℕ := 8*128^D
    have e : 2^k≤C*(k+2)^(D+1)*(L+1)^D := calc
      _ ≤ _ := h
      _ ≤ 8*(k+2)*(base k L)^D := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by simp only [base,mul_pow,C,pow_succ];ring
    have z:=Nat.pow_le_pow_left e 2
    have powers : ((k+2)^(D+1))^2 ≤ 2^k*4 := by
      rw [←pow_mul,mul_comm (D+1) 2,←show (2:ℕ)^(k+2)=2^k*4 by rw [pow_add];rfl]
      exact grow
    have w : 2^k*2^k ≤ 2^k*((16*128^D)^2*(L+1)^(2*D)) := calc
      _ = (2^k)^2 := (sq _).symm
      _ ≤ _ := z
      _ = C^2*((k+2)^(D+1))^2*((L+1)^D)^2 := by ring
      _ ≤ C^2*(2^k*4)*((L+1)^D)^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ powers)
      _ = _ := by rw [←pow_mul,mul_comm D 2];dsimp [C];ring
    exact (Nat.le_of_mul_le_mul_left w (Nat.two_pow_pos k)).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  · have top : k≤16*(D+2)^2+8:=by omega
    have bounded := Nat.pow_le_pow_right (by decide : 1≤2) top
    exact bounded.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _ pos))

private theorem all_k {k L D : ℕ}
    (coarse : 8≤k → G k < 8*(k+1)*(base k L)^D) :
    2^k ≤constant D*(L+1)^(2*D) := by
  by_cases hk : 8≤k
  · have h := coarse hk
    have ge : 2^k≤G k:=by
      have := Nat.two_pow_pos k
      dsimp [G];rw [pow_succ];omega
    exact eliminate (ge.trans h.le)
  · have : 2^k≤(2:ℕ)^8:=Nat.pow_le_pow_right (by decide) (by omega)
    have high : (2:ℕ)^8≤2^(16*(D+2)^2+8):=Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
    exact this.trans (high.trans ((Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_right _
      (pow_pos (by omega) _))))

theorem original (k L : ℕ) (p e : Fin 3→ℕ) (prime : ∀ i,(p i).Prime)
    (odd : ∀ i,Odd (p i)) (distinct : p.Injective) (positive : ∀i,0<e i)
    (longest : ∃ i,e i+1=L) (cap : ∀i,e i+1≤L)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k≤constant degree*(L+1)^(2*degree) := by
  apply all_k
  intro hk
  let c : Family := ⟨p,e,k,L,prime,positive,hk,longest,cap,distinct⟩
  exact OMA.SingleMovingOriginal245212.coarse c odd eqn

end OMA.SingleMovingHeight245212

end


/- A largest exponent on the smallest odd prime -/

section

/- The ordinary moments at the other two primes can never reverse the sign
for the smallest base when it carries the longest exponent. -/
namespace OMA.LeastTallFactor245212
open Nat Finset OMA.TwoTallLocal245212 OMA.SingleMovingGap245212
open OMA.Smooth245212 (X Y y_nonneg)
open OMA.ThreeMovingLocal245212 (yy yn den)
open OMA.ThreeMovingLocal245212 (quotients)

theorem localY {p e : ℕ} (hp : p.Prime) (he : 0<e) (big : 33≤p) (mode : Option Bool) :
    yy' p e mode≤33/64 := by
  have pr : (33:ℚ)≤p:=by exact_mod_cast big
  have ep : (1:ℚ)≤e:=by exact_mod_cast he
  have B : (0:ℚ)<(e:ℚ)+1:=by positivity
  have u : (0:ℚ)<(p:ℚ)-1:=by linarith
  have yn : yy p e true = (p:ℚ)/(((e:ℚ)+1)*(p-1)) := by
    dsimp [yy,OMA.ThreeMovingLocal245212.yn,den]
    push_cast [Nat.cast_sub hp.one_le];field_simp
  have yb : yy p e true≤33/64 := by
    rw [yn,div_le_iff₀ (mul_pos B u)]
    nlinarith only [pr,mul_nonneg (sub_nonneg.mpr ep) u.le]
  rcases mode with _|b
  · have q:=(OMA.ThreeMovingLocal245212.quotients (e:=e) hp).2
    change Y p (some e)≤33/64
    have pw : 0< (p:ℚ)^e := by positivity
    have dn : 0≤1/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e):=by positivity
    linarith only [q,mul_nonneg u.le dn,yb]
  · cases b
    · change yy p e false≤_
      simp [yy,OMA.ThreeMovingLocal245212.yn,den]
      rw [←one_div];apply (div_le_iff₀ B).mpr;linarith only [ep]
    · exact yb

theorem localX {z p e : ℕ} (zp : 33≤z) (le : z≤p) (hp : p.Prime) (ep : 0<e) :
    1≤X p (some e) ∧ X p (some e)≤33/32 ∧ ((z:ℚ)-1)*(X p (some e)-1)≤1 := by
  have low : 1≤X p (some e):=(ranges hp ep none).1
  have zlow : (32:ℚ)≤(z:ℚ)-1:=by
    have h : (33:ℚ)≤z:=by exact_mod_cast zp
    linarith
  have v : (z:ℚ)≤p:=by exact_mod_cast le
  have den : (0:ℚ)<(p:ℚ)-1:=by linarith
  have eq : ((p:ℚ)-1)*(X p (some e)-1) = 1-Y p (some e) := by
    dsimp [X];field_simp;ring
  have Y0:=y_nonneg hp.one_lt (some e)
  have h : ((z:ℚ)-1)*(X p (some e)-1)≤1 := by
    nlinarith only [eq,Y0,mul_nonneg (sub_nonneg.mpr v) (sub_nonneg.mpr low)]
  refine ⟨low,?_,h⟩
  nlinarith only [h,mul_nonneg (sub_nonneg.mpr zlow) (sub_nonneg.mpr low)]

theorem margin (c : Family) {f g : ℕ} {v : Fin 3} (long : c.e v+1=c.L)
    (least : ∀i,c.p v≤c.p i) (large : 33≤c.p v) (tall : 32≤c.L) (gp : 0<g)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    (g:ℚ)*((c.p v:ℚ)-1)*(33/64)^2 < f := by
  let P:=∏i,exactX c i
  let S:=∏i,exactY c i
  let u:ℚ:=(c.p v:ℚ)-1
  have loc i := localX large (least i) (c.prime i) (c.positive i)
  change ∀i, 1≤exactX c i ∧ exactX c i≤33/32 ∧ u*(exactX c i-1)≤1 at loc
  have p0 i := (zero_le_one.trans (loc i).1)
  have Xprod : u*(P-1) ≤ 13/4 := by
    let x:=exactX c
    have a:=mul_le_mul_of_nonneg_right (loc 0).2.2 (mul_nonneg (p0 1) (p0 2))
    have b:=mul_le_mul_of_nonneg_right (loc 1).2.2 (p0 2)
    have d:=mul_le_mul (loc 1).2.1 (loc 2).2.1 (p0 2) (by norm_num : (0:ℚ)≤33/32)
    dsimp only [P];rw [Fin.prod_univ_three]
    nlinarith only [a,b,d,(loc 2).2.2,(loc 2).2.1]
  have nonY i : 0≤exactY c i := (ranges (c.prime i) (c.positive i) none).2.2.1
  have bound i : exactY c i≤1 := (localY (c.prime i) (c.positive i) (large.trans (least i)) none).trans (by norm_num)
  have s := (ranges (c.prime v) (c.positive v) none).2.2.2
  change exactY c v≤2/((c.e v:ℚ)+1) at s
  have T : (32:ℚ)≤(c.e v:ℚ)+1:=by exact_mod_cast (long ▸ tall : 32≤c.e v+1)
  have lowS : S≤1/16 := by
    calc
      _ = (∏ i∈univ.erase v,exactY c i)*exactY c v := (prod_erase_mul _ _ (mem_univ v)).symm
      _ ≤ exactY c v := mul_le_of_le_one_left (nonY v) (prod_le_one (fun j _=>nonY j) (fun j _=>bound j))
      _ ≤ _ := s.trans ((div_le_iff₀ (by positivity)).mpr (by linarith only [T]))
  change (f:ℚ)*P+(g:ℚ)*S=(f+g:ℕ) at actual
  push_cast at actual
  have m : 0≤P-1:=sub_nonneg.mpr (one_le_prod (fun i _=>(loc i).1))
  have g0 : (0:ℚ)<g:=by exact_mod_cast gp
  by_contra! neg
  change (f:ℚ)≤(g:ℚ)*u*(33/64)^2 at neg
  nlinarith only [actual,mul_le_mul_of_nonneg_right neg m,mul_le_mul_of_nonneg_left Xprod g0.le,
    mul_le_mul_of_nonneg_left lowS g0.le,g0]

end OMA.LeastTallFactor245212

end

section

/- Strict restoration when the smallest base carries the longest exponent. -/

namespace OMA.LeastTallStrict245212
open Nat Finset OMA.TwoTallLocal245212 OMA.SingleMovingGap245212
open OMA.ThreeMovingLocal245212 (xx yy xn yn den)
open OMA.Smooth245212
open OMA.Abundance245212
open ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingLocal245212 (quotients)

private theorem upward {p e f g k : ℕ} (hp : p.Prime) (pe : 0<e)
    (ku : 0<k) (gu : 0<g) (fk : k*g≤f) (b : Bool)
    (x x' y y' : ℚ) (x0 : 1≤x) (x1 : 1≤x') (y0 : 0≤y) (y1 : 0≤y')
    (slope : b=true → (g:ℚ)*((p:ℚ)-1)*(y*y') < f) :
    (f:ℚ)*xx p e b*x*x'+g*yy p e b*y*y' < f*X p (some e)*x*x'+g*Y p (some e)*y*y' := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have fg : (k:ℚ)*g≤f:=by exact_mod_cast fk
  have g0 : (0:ℚ)<g:=by exact_mod_cast gu
  have kp : (0:ℚ)<k:=by exact_mod_cast ku
  have fm : (0:ℚ)<f := lt_of_lt_of_le (mul_pos kp g0) fg
  have xl : (1:ℚ)≤x*x' := one_le_mul_of_one_le_of_one_le x0 x1
  have ylo := mul_nonneg y0 y1
  cases b with
  | false =>
    have ysum : 1/((e:ℚ)+1)≤Y p (some e) := by
      have id:=y_factor hp e
      have big : (p:ℚ)^e ≤ σ 1 (p^e) := by
        exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,Finset.sum_range_succ];omega)
      apply (div_le_iff₀ (by positivity : (0:ℚ)<(e:ℚ)+1)).mpr
      apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
      nlinarith only [id,big]
    have ylt := y_strict hp.one_lt (show 0<e from pe)
    have xstrict : 1<X p (some e) := by
      dsimp [X];apply lt_add_of_pos_right;apply _root_.div_pos _ (by linarith)
      exact sub_pos.mpr (ylt.trans_le (y_one hp.one_lt _))
    have minus : 0<(f:ℚ)*(X p (some e)-1)*(x*x') := by positivity
    have plus := mul_nonneg (mul_nonneg g0.le (sub_nonneg.mpr ysum)) ylo
    have xx0 : xx p e false=1 := by simp [xx,xn,den,show (e:ℚ)+1≠0 by positivity]
    have yy0 : yy p e false=1/((e:ℚ)+1) := by simp [yy,yn,den]
    rw [xx0,yy0]
    nlinarith only [minus,plus]
  | true =>
    let u:ℚ:=(p:ℚ)-1
    let d:ℚ:=1/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
    have dp : 0<d := by dsimp [d,u];positivity
    have us : (0:ℚ)≤u:=by dsimp [u];linarith
    have diff : 0<(f:ℚ)*x*x'-g*u*y*y' := by
      nlinarith only [mul_le_mul_of_nonneg_left xl fm.le,slope rfl]
    have q:=OMA.ThreeMovingLocal245212.quotients hp (e:=e)
    change X p (some e)=xx p e true+d ∧ Y p (some e)=yy p e true-u*d at q
    rw [q.1,q.2]
    nlinarith only [mul_pos dp diff]


theorem descend (c : Family) (b : Fin 3→Option Bool) (f g : ℕ) (gp : 0<g) (fg : c.k*g≤f)
    (long : c.e 0+1=c.L) (least : ∀i,c.p 0≤c.p i) (large : 33≤c.p 0) (tall : 32≤c.L)
    (moving : b 0≠none) (small : ∀i,b i=some true → c.p i≤ max (c.k+1) c.L)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    score f g (x' c b) (y' c b)<score f g (exactX c) (exactY c) := by
  let mix (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactX c i else x' c b i
  let miy (s : Finset (Fin 3)) (i : Fin 3) := if i∈s then exactY c i else y' c b i
  have cap (s : Finset (Fin 3)) (i) : miy s i≤33/64 := by
    by_cases si:i∈s
    · simpa only [miy,if_pos si,exactY,yy'] using
        OMA.LeastTallFactor245212.localY (c.prime i) (c.positive i) (large.trans (least i)) none
    · simpa only [miy,if_neg si,y'] using
        OMA.LeastTallFactor245212.localY (c.prime i) (c.positive i) (large.trans (least i)) (b i)
  have adv (s : Finset (Fin 3)) {i} (fresh : i∉s) (bit : Bool) (bi : b i=some bit) :
      score f g (mix s) (miy s)<score f g (mix (insert i s)) (miy (insert i s)) := by
    have bound j : 1≤ mix s j ∧ 0≤ miy s j ∧ miy s j≤2/((c.e j:ℚ)+1) := by
      by_cases mem : j∈s
      · have v:=ranges (c.prime j) (c.positive j) none
        simpa only [mix,miy,if_pos mem,exactX,exactY,xx',yy'] using And.intro v.1 v.2.2
      · have v:=ranges (c.prime j) (c.positive j) (b j)
        simpa only [mix,miy,if_neg mem,x',y'] using And.intro v.1 v.2.2
    have single {j l : Fin 3} (n : j≠i) (n' : l≠i) (jl : j≠l) :
        (f:ℚ)*mix s i*mix s j*mix s l+g*miy s i*miy s j*miy s l <
        f*mix (insert i s) i*mix (insert i s) j*mix (insert i s) l+
          g*miy (insert i s) i*miy (insert i s) j*miy (insert i s) l := by
      have step:=upward (c.prime i) (c.positive i) (by have:=c.kp;omega : 0<c.k) gp fg bit
        (mix s j) (mix s l) (miy s j) (miy s l) (bound j).1 (bound l).1 (bound j).2.1 (bound l).2.1
      suffices slope : bit=true → (g:ℚ)*((c.p i:ℚ)-1)*(miy s j*miy s l) < f by
        simpa [mix,miy,exactX,exactY,x',y',xx',yy',fresh,n,n',bi] using step slope
      intro on
      have up :=small i (on ▸ bi)
      have upos : 0≤(c.p i:ℚ)-1:=by
        have t : (1:ℚ)≤c.p i:=by exact_mod_cast (c.prime i).one_le
        linarith
      by_cases iz : i=0
      · subst i
        have mm:=OMA.LeastTallFactor245212.margin c long least large tall gp actual
        have h:=mul_le_mul (cap s j) (cap s l) (bound l).2.1 (by norm_num : (0:ℚ)≤33/64)
        rw [sq] at mm
        exact (mul_le_mul_of_nonneg_left h (mul_nonneg (by positivity) upos)).trans_lt mm
      · have zeroPerm : j=0 ∨ l=0:=by omega
        have hl : (miy s j*miy s l)*(c.L:ℚ)≤2 := by
          have at0 := (le_div_iff₀ (by positivity)).mp (bound 0).2.2
          have L : (c.L:ℚ)=(c.e 0:ℚ)+1:=by exact_mod_cast long.symm
          have u j : miy s j≤1:=(cap s j).trans (by norm_num)
          rcases zeroPerm with rfl|rfl
          · nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (u l) (bound 0).2.1)
              (Nat.cast_nonneg (α:=ℚ) c.L),L ▸ at0]
          · nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (u j) (bound 0).2.1)
              (Nat.cast_nonneg (α:=ℚ) c.L),L ▸ at0]
        have g0 : (0:ℚ)<g:=by exact_mod_cast gp
        have fk : (c.k:ℚ)*g≤f:=by exact_mod_cast fg
        have k8 : (8:ℚ)≤c.k:=by exact_mod_cast c.kp
        have hprod := mul_nonneg (bound j).2.1 (bound l).2.1
        have pq : ((c.p i:ℚ)-1)*(miy s j*miy s l)<c.k := by
          rcases (le_max_iff.mp up) with ks|ls
          · have v:(c.p i:ℚ)≤c.k+1:=by exact_mod_cast ks
            have h:=mul_le_mul (cap s j) (cap s l) (bound l).2.1 (by norm_num : (0:ℚ)≤33/64)
            nlinarith only [mul_le_mul_of_nonneg_right (by linarith : (c.p i:ℚ)-1≤c.k) hprod,
              mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℚ) c.k),k8]
          · have v:(c.p i:ℚ)≤c.L:=by exact_mod_cast ls
            nlinarith only [hl,mul_le_mul_of_nonneg_right v hprod,hprod,k8]
        nlinarith only [mul_lt_mul_of_pos_left pq g0,fk]
    dsimp [OMA.SingleMovingGap245212.score];simp only [Fin.prod_univ_three]
    have choice : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choice with rfl|rfl|rfl
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=1) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=2) (by decide) (by decide) (by decide)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using single (j:=0) (l:=1) (by decide) (by decide) (by decide)
  have advance (s : Finset (Fin 3)) {i} (fresh : i∉s) :
      score f g (mix s) (miy s)≤ score f g (mix (insert i s)) (miy (insert i s)) := by
    cases h:b i with
    | some bit=>exact (adv s fresh bit h).le
    | none=>
      have eq (j : Fin 3) : mix s j=mix (insert i s) j ∧ miy s j=miy (insert i s) j := by
        by_cases n:j=i
        · subst j;simp [mix,miy,fresh,x',y',exactX,exactY,h,xx',yy']
        · simp [mix,miy,n]
      rw [funext (fun j=>(eq j).1),funext (fun j=>(eq j).2)]
  obtain ⟨bit,b0⟩:=Option.ne_none_iff_exists'.mp moving
  have a:=adv ∅ (i:=0) (by decide) bit b0
  have b1:=advance {0} (i:=1) (by decide)
  have d:=advance {1,0} (i:=2) (by decide)
  have un : insert (2:Fin 3) ({1,0}:Finset (Fin 3))=univ:=by decide
  rw [un] at d
  simpa [mix,miy] using ((a.trans_le b1).trans_le d)

end OMA.LeastTallStrict245212

end

section

/- Six-scale separation when only a specified long coordinate must move. -/
namespace OMA.LeastTallStep245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212
open OMA.TwoTallScalar245212 (cut cut_mono cut_succ)
open OMA.SingleMovingStep245212 (empty_six degree)
open OMA.SingleMovingStep245212 (integer_gap)
open OMA.SingleMovingStep245212 (difference)
theorem contradiction (c : Family) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (separated : ∀ b, b 0≠none → (f+g)*dust c b ≠ f*NX c b+g*NY c b)
    (longPower : x^degree<c.p 0^c.e 0)
    (close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^degree:ℕ):ℚ)) : False := by
  let point : Fin 6 → ℕ := ![c.p 0,c.p 1,c.p 2,c.p 0^c.e 0,c.p 1^c.e 1,c.p 2^c.e 2]
  obtain ⟨j,band⟩:=empty_six x (by omega) point
  have bp (i:Fin 3) : c.p i≤cut x j.val ∨ cut x (j.val+1)<c.p i := by
    fin_cases i <;> first | exact band 0 | exact band 1 | exact band 2
  have bd (i:Fin 3) : c.p i^c.e i≤cut x j.val ∨ cut x (j.val+1)<c.p i^c.e i := by
    fin_cases i <;> first | exact band 3 | exact band 4 | exact band 5
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^degree:=cut_mono (by omega) (show j.val+1≤7 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simpa [lo] using ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^9 := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have maxcut : Q≤x^degree:=cut_mono (by omega) (show j.val≤7 by omega)
  have off : ¬c.p 0^c.e 0≤Q:=(maxcut.trans_lt longPower).not_ge
  have nz:=separated b (by simp [b,off])
  have iga:=OMA.SingleMovingStep245212.integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=OMA.SingleMovingStep245212.difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega


end OMA.LeastTallStep245212

end

section

/- Absorb all polynomial scales into a single sufficiently long prime power. -/
namespace OMA.LeastTallScale245212
open Nat
open OMA.ThreeMovingOriginal245212 (F G)

def cutoff (C E D : ℕ) :=
  2*(512*(C+1)^2)^D+16*((2*E+1)*D+1)^2+64

theorem scale {C E D k L p e : ℕ} (dyadic : 2^k≤C*(L+1)^E)
    (large : cutoff C E D≤L) (hp : 2≤p) (long : e+1=L) :
    (128*(F k+G k+1)*(L+1))^D<p^e := by
  let w:=2^k
  have wp : 0<w:=Nat.two_pow_pos _
  have kw : k+1≤w:=Nat.lt_pow_self (by decide)
  have id : F k+G k=(k+1)*(2*w) := by
    have sub:=Nat.sub_add_cancel (show 1≤2*w by omega)
    dsimp [F,G];rw [pow_succ,←show w=2^k by rfl]
    nlinarith only [sub,Nat.sub_add_cancel (by omega : 1≤w*2)]
  have v : F k+G k+1≤4*w^2:=by
    rw [id]
    nlinarith only [Nat.mul_le_mul_right (2*w) kw,Nat.one_le_pow 2 w wp]
  let A := (512*(C+1)^2)^D
  let B := (2*E+1)*D
  have pre : 128*(F k+G k+1)*(L+1) ≤ 512*(C+1)^2*(L+1)^(2*E+1) := calc
    _ ≤ 128*(4*w^2)*(L+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ v)
    _ ≤ 128*(4*((C+1)*(L+1)^E)^2)*(L+1) := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (dyadic.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))) _
    _ = _ := by rw [pow_succ (L+1) (2*E),mul_comm 2 E,pow_mul];ring
  have upper : (128*(F k+G k+1)*(L+1))^D ≤ A*(L+1)^B := by
    simpa only [A,B,mul_pow,pow_mul] using Nat.pow_le_pow_left pre D
  change 2*A+16*(B+1)^2+64≤L at large
  have absorb:=OMA.ComplementarySize245212.absorb (d:=B) (b:=L+1) (by omega)
  have grow : A^2≤2^(2*A) := by
    rw [mul_comm 2 A,pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1<2)).le 2
  have small : 2*A+(L+1)<e*2:=by omega
  have sq : (A*(L+1)^B)^2<(p^e)^2 := calc
    _ = A^2*(L+1)^(2*B) := by rw [mul_pow,mul_comm 2 B,pow_mul (L+1) B 2]
    _ ≤ 2^(2*A)*2^(L+1) := Nat.mul_le_mul grow absorb
    _ = 2^(2*A+(L+1)) := (pow_add ..).symm
    _ < 2^(e*2) := Nat.pow_lt_pow_right (by decide) small
    _ ≤ _ := by rw [pow_mul];exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hp e) 2
  exact upper.trans_lt ((pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp sq)

end OMA.LeastTallScale245212

end

section

/- Effective absolute finiteness when the smallest odd prime carries a
largest exponent: all primes, all exponents and the dyadic exponent may move. -/
namespace OMA.LeastTallOriginal245212
open Nat Finset ArithmeticFunction OMA.SingleMovingGap245212
open OMA.Smooth245212 (total)
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.SingleMovingStep245212 (degree)
open OMA.SingleMovingHeight245212 (constant)
open OMA.SingleMovingOriginal245212 (identities)
open scoped ArithmeticFunction.sigma

private theorem out (c : Family) {C E : ℕ} (wide : 2^c.k≤C*(c.L+1)^E)
    (long : c.e 0+1=c.L) (least : ∀i,c.p 0≤c.p i) (large : 33≤c.p 0)
    (op : ∀i,Odd (c.p i))
    (eqn : OeisA245212.a (2^c.k*total c.p c.e)=(σ 1 (2^c.k*total c.p c.e):ℤ)) :
    c.L < OMA.LeastTallScale245212.cutoff C E degree := by
  by_contra! big
  let f:=F c.k
  let g:=G c.k
  let x:=128*(f+g+1)*(c.L+1)
  have tg:=OMA.SingleMovingOriginal245212.identities c.k
  have actual:=OMA.SingleMovingOriginal245212.physical c c.k op c.inj eqn
  have pwr:=OMA.LeastTallScale245212.scale wide big (c.prime 0).two_le long
  have h32 : 32≤c.L := by
    apply le_trans _ big
    exact (Nat.le_add_left 64 _).trans' (by decide : 32≤64)
  apply OMA.LeastTallStep245212.contradiction c f g x _ _ _ _ pwr
    (by rw [actual,sub_self,abs_zero];positivity)
  · dsimp only [x];nlinarith only [Nat.zero_le ((f+g)*c.L),Nat.zero_le (f+g),Nat.zero_le c.L]
  · dsimp only [x];nlinarith only [Nat.zero_le ((f+g)*c.L),Nat.zero_le (f+g),Nat.zero_le c.L]
  · dsimp only [x];nlinarith only [Nat.zero_le ((f+g)*c.L),Nat.zero_le (f+g),Nat.zero_le c.L]
  · intro b moving hit
    have unit i : ¬c.p i∣2^(c.k+1):=by
      intro dvd
      have d:=(c.prime i).dvd_of_dvd_pow dvd
      exact (Nat.not_dvd_of_pos_of_lt (by decide) (by have:=large.trans (least i);omega : 2<c.p i)) d
    have retained := OMA.SingleMovingGap245212.retained tg.2.1 unit hit
    have less:=(OMA.LeastTallStrict245212.descend c b f g tg.1 (by have:=tg.2.2;dsimp [f,g];omega)
      long least large h32 moving retained actual).trans_le actual.le
    have val := clear c b f g
    have same : ((f+g:ℕ):ℚ)*dust c b=((f*NX c b+g*NY c b:ℕ):ℚ) := by exact_mod_cast hit
    exact (ne_of_lt (mul_lt_mul_of_pos_right less (show (0:ℚ)<dust c b by exact_mod_cast dust_pos c b))) (val.trans same.symm)

def value (C E : ℕ) := (∑ j∈range 67, OMA.RankThreeEffective245212.bound j)+
  OMA.TwoTallFinite245212.valueCap (OMA.LeastTallScale245212.cutoff C E degree)

private theorem sector (C E k : ℕ) (p e : Fin 3→ℕ) (hp : ∀i,(p i).Prime) (op : ∀i,Odd (p i)) (inj : p.Injective)
    (he : ∀i,0<e i) (least : ∀i,p 0≤p i) (long : ∀i,e i≤e 0)
    (power : 2^k≤C*(e 0+2)^E)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k*total p e≤value C E := by
  classical
  have odd : Odd (total p e) := Nat.coprime_two_left.mp
    (Coprime.prod_right (fun i _ => (Nat.coprime_two_left.mpr (op i)).pow_right _))
  have dvd i : p i∣total p e := (dvd_pow_self _ (he i).ne').trans
    (dvd_prod_of_mem (fun j => p j^e j) (mem_univ i))
  have big : 1<total p e := (hp 0).one_lt.trans_le (Nat.le_of_dvd odd.pos (dvd 0))
  have image : (total p e).primeFactors=univ.image p := by
    ext q
    constructor
    · intro mem
      have pr:=prime_of_mem_primeFactors mem
      obtain ⟨i,_,di⟩:=(pr.prime.dvd_finsetProd_iff _).mp (dvd_of_mem_primeFactors mem :
        q∣∏i,p i^e i)
      exact mem_image.mpr ⟨i,mem_univ _,((prime_dvd_prime_iff_eq pr (hp i)).mp (pr.dvd_of_dvd_pow di)).symm⟩
    · rintro mem
      obtain ⟨i,_,rfl⟩:=mem_image.mp mem
      exact mem_primeFactors.mpr ⟨hp i,dvd i,odd.pos.ne'⟩
  by_cases low : k≤66
  · have rk : (total p e).primeFactors.card=3:=by rw [image,card_image_of_injective _ inj];simp
    have sz:=OMA.RankThreeEffective245212.original odd rk eqn
    exact sz.trans ((single_le_sum (f:=OMA.RankThreeEffective245212.bound) (fun _ _=>Nat.zero_le _)
      (mem_range.mpr (show k<67 by omega))).trans (Nat.le_add_right _ _))
  have k0:=OMA.DyadicLeast245212.exponent_lt_twice_prime odd (mem_primeFactors.mpr ⟨hp 0,dvd 0,odd.pos.ne'⟩) eqn
  let L := e 0+1
  have lengths i : e i+1≤L:=Nat.succ_le_succ (long i)
  let c : Family := ⟨p,e,k,L,hp,he,by omega,⟨0,rfl⟩,lengths,inj⟩
  have high : L<OMA.LeastTallScale245212.cutoff C E degree := out c power rfl least (by change 33≤p 0;omega) op eqn
  have sm:=OMA.TwoTallFinite245212.bounded (c:=OMA.LeastTallScale245212.cutoff C E degree) (m:=1) (L:=L) p e hp op inj he (by decide)
    (fun _ _=>Nat.succ_pos _) lengths (high.le.trans_eq (Nat.mul_one _).symm) eqn
  exact sm.trans (Nat.le_add_left _ _)

def bound := value (constant degree) (2*degree)

theorem original (k : ℕ) (p e : Fin 3→ℕ) (hp : ∀i,(p i).Prime) (op : ∀i,Odd (p i)) (inj : p.Injective)
    (he : ∀i,0<e i) (least : ∀i,p 0≤p i) (long : ∀i,e i≤e 0)
    (eqn : OeisA245212.a (2^k*total p e)=(σ 1 (2^k*total p e):ℤ)) :
    2^k*total p e≤bound := by
  apply sector _ _ k p e hp op inj he least long _ eqn
  exact OMA.SingleMovingHeight245212.original k (e 0+1) p e hp op inj he ⟨0,rfl⟩
    (fun i=>Nat.succ_le_succ (long i)) eqn

end OMA.LeastTallOriginal245212

end


/- Forced exact/retained/discarded rank-three configuration -/

section

/- Explicit cutoff at which two exactly kept short factors are impossible,
and the surviving exact cofactor has polynomial height with leading constant one. -/
namespace OMA.MiddleCut245212
open Nat Finset ArithmeticFunction OMA.SingleMovingGap245212
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.Smooth245212 (total W)
open OMA.PairHeight245212 (moment_bound)

def cutoff (C E D : ℕ) := C+512+OMA.LeastTallScale245212.cutoff C E (20*D)

def scale (k L : ℕ) := 128*(F k+G k+1)*(L+1)
def exponent (E D : ℕ) := (E+1)+(2*(E+1)+3)*D

theorem size {C E D k L : ℕ} (high : cutoff C E D≤L) (dyad : 2^k≤C*(L+1)^E)
    (y : ℕ) (yp : y≤(scale k L)^D) : 2^k*y≤(L+1)^(exponent E D) := by
  have cl : C≤L+1 := by dsimp [cutoff] at high;omega
  have b : 512≤L+1:=by dsimp [cutoff] at high;omega
  let t:=2^k
  have tp : 0<t:=Nat.two_pow_pos k
  have dk : t≤(L+1)^(E+1):=by
    rw [pow_succ'];exact dyad.trans (Nat.mul_le_mul_right _ cl)
  have kg : G k≤2*t := by dsimp [G,t];rw [pow_succ];omega
  have kcap : k+1≤t:=Nat.lt_pow_self (by decide)
  have bound : F k+G k+1≤4*t^2:=by
    dsimp only [F];rw [pow_succ,←show t=2^k by rfl]
    nlinarith only [kg,Nat.mul_le_mul_right (2*t) kcap,Nat.one_le_pow 2 t tp]
  have sc : scale k L≤(L+1)^(2*(E+1)+3) := calc
    _ ≤ 128*(4*t^2)*(L+1):=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bound)
    _ ≤ (L+1)^2*((L+1)^(E+1))^2*(L+1):=by
      have bs : 512 ≤ (L+1)^2:=b.trans (Nat.le_self_pow (by decide) _)
      nlinarith only [Nat.mul_le_mul_right (L+1) (Nat.mul_le_mul bs (Nat.pow_le_pow_left dk 2))]
    _ = _:=by rw [pow_add (L+1) (2*(E+1)) 3,mul_comm 2 (E+1),pow_mul (L+1) (E+1) 2];ring
  dsimp [exponent]
  rw [pow_add,pow_mul]
  exact Nat.mul_le_mul dk (yp.trans (Nat.pow_le_pow_left sc D))

theorem power {C E D k L q b : ℕ} (dp : 1≤D) (dyad : 2^k≤C*(L+1)^E)
    (high : cutoff C E D≤L) (long : b+1=L) (qp : 2≤q) :
    k+1≤L ∧ 2^k≤ scale k L ∧ L≤ scale k L ∧ 128≤ scale k L ∧ 
    (scale k L)^(20*D)<q^b := by
  have ln : OMA.LeastTallScale245212.cutoff C E (20*D)≤L:=by dsimp [cutoff] at high;omega
  have large:=OMA.LeastTallScale245212.scale dyad ln (by decide : 2≤2) long
  have base : 2^k≤G k:=by dsimp [G];rw [pow_succ];have:=Nat.two_pow_pos k;omega
  let x:=scale k L
  have x1 : 2^k≤x ∧ L≤x ∧ 128≤x := by
    dsimp [x,scale]
    constructor
    · nlinarith only [base,Nat.zero_le (F k),Nat.zero_le L,Nat.zero_le ((F k+G k)*L)]
    constructor <;> nlinarith only [Nat.zero_le (F k),Nat.zero_le (G k),Nat.zero_le L,Nat.zero_le ((F k+G k)*L)]
  have gain : 2^k<2^b:= x1.1.trans_lt ((Nat.le_self_pow (by omega : 20*D≠0) x).trans_lt large)
  have kin := (pow_lt_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp gain
  exact ⟨by omega,x1.1,x1.2.1,x1.2.2,large.trans_le (Nat.pow_le_pow_left qp b)⟩

theorem not_both {k p q r a b d Q x D : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (odd : Odd q) (pq : p<q) (qr : q<r) (bp : 0<b) (dp : 1≤D) (xb : 2≤x)
    (dyad : 2^k≤x) (bound : Q≤x^D) (power : x^(20*D)<q^b)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    ¬(p^a≤Q ∧ r^d≤Q) := by
  rintro ⟨pa,rd⟩
  let m:=2^k*p^a*r^d
  let Z:=x^D
  have pow0 : 2≤Z:=xb.trans (Nat.le_self_pow (by omega : D≠0) _)
  have mB : m≤Z^3:=by
    calc
      _ ≤ Z*Z*Z:=Nat.mul_le_mul (Nat.mul_le_mul (dyad.trans (Nat.le_self_pow (by omega : D≠0) _)) (pa.trans bound)) (rd.trans bound)
      _ = _:=by ring
  have mp : 0< m:=by dsimp [m];have:=pp.pos;have:=rp.pos;positivity
  have cop : m.Coprime q:=(((Nat.coprime_two_left.mpr odd).pow_left k).mul_left
    (((Nat.coprime_primes pp qp).mpr pq.ne).pow_left a)).mul_left (((Nat.coprime_primes rp qp).mpr qr.ne').pow_left d)
  have boundQ:=OMA.PairHeight245212.last_square mp qp (by obtain ⟨z,h⟩:=odd;have:=qp.two_le;omega)
    cop bp (by simpa only [m,mul_comm,mul_left_comm,mul_assoc] using eqn)
  have moments:=OMA.PairHeight245212.moment_bound mp
  have h : q^b≤x^(20*D) := calc
    _ ≤ _:=boundQ
    _ ≤ (2*m^3)^2:=Nat.pow_le_pow_left moments 2
    _ ≤ (Z*(Z^3)^3)^2:=Nat.pow_le_pow_left (Nat.mul_le_mul pow0 (Nat.pow_le_pow_left mB 3)) 2
    _ = Z^20:=by ring
    _ = _:=by dsimp [Z];rw [←pow_mul,mul_comm D 20]
  omega

end OMA.MiddleCut245212

end

section

/- A polynomial-width interval around all six scales furnishes an exact mixed equality. -/
namespace OMA.MiddleWitness245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212
open OMA.TwoTallScalar245212 (cut cut_mono cut_succ)
open OMA.SingleMovingStep245212 (empty_six degree)
open OMA.SingleMovingStep245212 (integer_gap)
open OMA.SingleMovingStep245212 (difference)
theorem witness (c : Family) (f g x : ℕ) (big : 128≤x) (cf : f+g≤x) (cl : c.L≤x)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    ∃ (b : Fin 3→Option Bool) (Q : ℕ), x≤Q ∧ Q≤x^degree ∧
    (∀ i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))) ∧
    (f+g)*dust c b=f*NX c b+g*NY c b := by
  have close : |score f g (exactX c) (exactY c)-(f+g:ℕ)| ≤ 1/((x^degree:ℕ):ℚ):=by
    rw [actual,sub_self,abs_zero];positivity
  let point : Fin 6 → ℕ := ![c.p 0,c.p 1,c.p 2,c.p 0^c.e 0,c.p 1^c.e 1,c.p 2^c.e 2]
  obtain ⟨j,band⟩:=empty_six x (by omega) point
  have bp (i:Fin 3) : c.p i≤cut x j.val ∨ cut x (j.val+1)<c.p i := by
    fin_cases i <;> first | exact band 0 | exact band 1 | exact band 2
  have bd (i:Fin 3) : c.p i^c.e i≤cut x j.val ∨ cut x (j.val+1)<c.p i^c.e i := by
    fin_cases i <;> first | exact band 3 | exact band 4 | exact band 5
  let Q:=cut x j.val
  let N:=cut x (j.val+1)
  let b (i:Fin 3) : Option Bool := if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q))
  have next : N=Q^16 := cut_succ x _
  have xQ : x≤Q := by
    have old:=cut_mono (show 1≤x by omega) (Nat.zero_le j.val)
    simpa [cut,Q] using old
  have np : 0<N := by rw [next];exact pow_pos (by omega) _
  have nb : N≤x^degree:=cut_mono (by omega) (show j.val+1≤7 by omega)
  have space (i) (t:Bool) (mode:b i=some t) : N ≤ (if t then c.p i^c.e i else c.p i) := by
    dsimp [b] at mode
    split at mode
    next=>contradiction
    next off=>
      obtain rfl:=Option.some.inj mode
      by_cases lo : c.p i≤Q
      · simp [lo]
        exact ((bd i).resolve_left off).le
      · simpa [lo] using ((bp i).resolve_left lo).le
  have ds : dust c b≤Q^9 := by
    have per i : Dn (c.p i) (c.e i) (b i)≤Q^3 := by
      have el := (c.cap i).trans (cl.trans xQ)
      by_cases exactMode : c.p i^c.e i≤Q
      · rw [show b i=none from if_pos exactMode]
        change (c.e i+1)*(c.p i^c.e i)≤Q^3
        exact
          (Nat.mul_le_mul el exactMode).trans (show Q*Q≤Q^3 by rw [←sq];exact Nat.pow_le_pow_right (by omega) (by decide))
      · by_cases keep:c.p i≤Q
        · simpa [b,exactMode,keep,Dn,den] using
            (Nat.mul_le_mul el (Nat.pow_le_pow_left (show c.p i-1≤Q by omega) 2)).trans_eq (by ring : Q*Q^2=Q^3)
        · simpa [b,exactMode,keep,Dn,den] using el.trans (Nat.le_self_pow (by decide : 3≠0) Q)
    dsimp [dust]
    exact (prod_le_prod' (fun i _=>per i)).trans_eq (by simp;ring)
  have maxcut : Q≤x^degree:=cut_mono (by omega) (show j.val≤7 by omega)
  refine ⟨b,Q,xQ,maxcut,(fun i=>rfl),?_⟩
  by_contra nz
  have iga:=OMA.SingleMovingStep245212.integer_gap c b f g nz
  let orig:=score f g (exactX c) (exactY c)
  let approx:=score f g (x' c b) (y' c b)
  let W:ℚ:=(f+g:ℕ)
  have lite : |orig-W|≤1/(N:ℚ) := close.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast nb))
  have diff:=OMA.SingleMovingStep245212.difference c b f g N np space
  change |approx-orig|≤_ at diff
  change (1:ℚ)≤|approx-W| * dust c b at iga
  have err : |approx-W| * (N:ℚ)≤48*((f:ℚ)+g)+1 := by
    have t:=abs_sub_le approx orig W
    have wn : (0:ℚ)<N:=by exact_mod_cast np
    nlinarith only [mul_le_mul_of_nonneg_right t wn.le,(le_div_iff₀ wn).mp diff,(le_div_iff₀ wn).mp lite]
  have sep : N≤(48*(f+g)+1)*dust c b := by
    have z : (N:ℚ)≤(48*((f:ℚ)+g)+1)*dust c b := by
      nlinarith only [mul_le_mul_of_nonneg_right iga (Nat.cast_nonneg N : (0:ℚ)≤N),
        mul_le_mul_of_nonneg_right err (Nat.cast_nonneg (dust c b) : (0:ℚ)≤_)]
    exact_mod_cast z
  have qr : 128≤Q:=big.trans xQ
  have cfq : f+g≤Q:=cf.trans xQ
  have cf' : 48*(f+g)+1<Q^2 := by
    nlinarith only [cfq,Nat.mul_le_mul_left Q qr,qr]
  have bad : N<Q^11 := sep.trans_lt ((Nat.mul_lt_mul_of_lt_of_le cf' ds (pow_pos (by omega) 9)).trans_eq (by ring))
  have natural : Q^11≤N:=next ▸ Nat.pow_le_pow_right (by omega) (by decide)
  omega



end OMA.MiddleWitness245212

end

section

/- Exact and one-sided changes on restoring one coordinate, with arbitrary
values of the other two moments already multiplied together. -/
namespace OMA.MiddleChange245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.TwoTallLocal245212
open OMA.ThreeMovingLocal245212 (xx yy xn yn den)
open scoped ArithmeticFunction.sigma
open OMA.ThreeMovingLocal245212 (quotients)

def inc (p e f g : ℕ) (b : Option Bool) (x y : ℚ) :=
  (f:ℚ)*(X p (some e)-xx' p e b)*x+(g:ℚ)*(Y p (some e)-yy' p e b)*y

theorem exact_inc (p e f g : ℕ) (x y : ℚ) : inc p e f g none x y=0 := by
  simp [inc,xx',yy']

theorem dropped {p e f g : ℕ} (hp : p.Prime) (ep : 0<e) {x y : ℚ} (xo : 1≤x) (yo : 0≤y) :
    (f:ℚ)/(2*p)≤ inc p e f g (some false) x y := by
  have ps : (0:ℚ)<p:=by exact_mod_cast hp.pos
  have B : (0:ℚ)<(e:ℚ)+1:=by positivity
  have low:=OMA.SingleMovingLoss245212.single_lb hp ep
  have low' : 1/(2*(p:ℚ))≤X p (some e)-1 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [low])
  have xx : xx' p e (some false)=1:=by simp [xx',OMA.ThreeMovingLocal245212.xx,xn,den,B.ne']
  have yy : yy' p e (some false)=1/((e:ℚ)+1):=by simp [yy',OMA.ThreeMovingLocal245212.yy,yn,den]
  have ys : 1/((e:ℚ)+1)≤Y p (some e):=by
    have id:=y_factor hp e
    have high : (p:ℚ)^e≤σ 1 (p^e):=by
      exact_mod_cast (show p^e ≤ σ 1 (p^e) by rw [sigma_one_apply_prime_pow hp,sum_range_succ];omega)
    apply (div_le_iff₀ B).mpr
    apply le_of_mul_le_mul_right (a:=(p:ℚ)^e) _ (by positivity)
    nlinarith only [id,high]
  rw [inc,xx,yy]
  have dy:=mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℚ) g) (sub_nonneg.mpr ys)) yo
  have dx : (f:ℚ)*(X p (some e)-1)≥f/(2*p):=by
    rw [div_eq_mul_inv,←one_div]
    exact mul_le_mul_of_nonneg_left low' (by positivity)
  nlinarith only [dx,dy,mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℚ) f)
    (le_trans (by positivity) low')) (sub_nonneg.mpr xo)]

theorem retained {p e f g : ℕ} (hp : p.Prime) (x y : ℚ) :
    inc p e f g (some true) x y =
      ((f:ℚ)*x-g*((p:ℚ)-1)*y)/(((e:ℚ)+1)*((p:ℚ)-1)^2*(p:ℚ)^e) := by
  have z:=OMA.ThreeMovingLocal245212.quotients (e:=e) hp
  rw [inc,z.1,z.2]; dsimp [xx',yy'];ring

theorem retained_loss {p e f g : ℕ} (hp : p.Prime) {x y : ℚ} (xo : 0≤x) (yo : y≤1) :
    -(g:ℚ)/(p:ℚ)^e ≤ inc p e f g (some true) x y := by
  have pp : (2:ℚ)≤p:=by exact_mod_cast hp.two_le
  let u:ℚ:=(p:ℚ)-1
  have up : 1≤u:=by dsimp [u];linarith
  have ppw : 0<(p:ℚ)^e:=by positivity
  rw [retained hp]
  change _≤(_-g*u*y)/(((e:ℚ)+1)*u^2*(p:ℚ)^e)
  apply (div_le_div_iff₀ ppw (by positivity)).mpr
  have sz : u ≤ ((e:ℚ)+1)*u^2 := by
    nlinarith only [mul_nonneg (zero_le_one.trans up) (sub_nonneg.mpr up),mul_nonneg (Nat.cast_nonneg (α:=ℚ) e) (sq_nonneg u),up]
  have v := mul_le_mul_of_nonneg_left yo (mul_nonneg (Nat.cast_nonneg (α:=ℚ) g) (by linarith : 0≤u))
  nlinarith only [mul_le_mul_of_nonneg_right v ppw.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sz (Nat.cast_nonneg (α:=ℚ) g)) ppw.le,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℚ) f) xo) ppw.le]

theorem retained_gain {p e f g k L : ℕ} (hp : p.Prime) (hk : 8≤k) (fg : k*g≤f)
    (base : p≤L) (len : e+1≤L) {x y : ℚ} (xo : 1≤x) (yo : 0≤y) (short : y*L≤2) :
    (g:ℚ)/((L:ℚ)^3*(p:ℚ)^e) ≤ inc p e f g (some true) x y := by
  have pp : (1:ℚ)<p:=by exact_mod_cast hp.one_lt
  have lp : (0:ℚ)<L:=by exact_mod_cast (hp.pos.trans_le base)
  let u:ℚ:=(p:ℚ)-1
  have up : 0<u:=by dsimp [u];linarith
  have ub : u≤L:=by
    have v : (p:ℚ)≤L:=by exact_mod_cast base
    dsimp [u];linarith
  have ecap : (e:ℚ)+1≤L:=by exact_mod_cast len
  have dx : ((e:ℚ)+1)*u^2 ≤(L:ℚ)^3:=by
    calc
      _ ≤ (L:ℚ)*(L:ℚ)^2:=mul_le_mul ecap (pow_le_pow_left₀ up.le ub _) (sq_nonneg _) lp.le
      _ = _ := by ring
  have fk : (k:ℚ)*g≤f:=by exact_mod_cast fg
  have k8 : (8:ℚ)≤k:=by exact_mod_cast hk
  have ft : (g:ℚ)≤(f:ℚ)*x-g*u*y:=by
    nlinarith only [mul_le_mul_of_nonneg_left xo (Nat.cast_nonneg (α:=ℚ) f),
      mul_le_mul_of_nonneg_left short (Nat.cast_nonneg (α:=ℚ) g),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ub yo) (Nat.cast_nonneg (α:=ℚ) g),
      mul_le_mul_of_nonneg_right k8 (Nat.cast_nonneg (α:=ℚ) g),fk,Nat.cast_nonneg (α:=ℚ) g]
  rw [retained hp]
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg g) (by dsimp [u] at *;positivity)
    (mul_le_mul_of_nonneg_right dx (by positivity))).trans (div_le_div_of_nonneg_right ft (by dsimp [u] at *;positivity))

end OMA.MiddleChange245212

end

section

/- Telescope the three changes in the order: middle prime, left prime, right prime. -/
namespace OMA.MiddleOrder245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212 OMA.MiddleChange245212

def others (exact approx : Fin 3→ℚ) (i : Fin 3) :=
  if i=1 then approx 0*approx 2 else if i=0 then exact 1*approx 2 else exact 0*exact 1

def otherX (c : Family) (b : Fin 3→Option Bool) := others (exactX c) (x' c b)
def otherY (c : Family) (b : Fin 3→Option Bool) := others (exactY c) (y' c b)
def change (c : Family) (b : Fin 3→Option Bool) (f g : ℕ) (i : Fin 3) :=
  inc (c.p i) (c.e i) f g (b i) (otherX c b i) (otherY c b i)

theorem zero_sum (c : Family) (b : Fin 3→Option Bool) (f g : ℕ)
    (hit : (f+g)*dust c b=f*NX c b+g*NY c b)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    change c b f g 1+change c b f g 0+change c b f g 2=0 := by
  have clr:=clear c b f g
  rw [←hit] at clr
  push_cast at clr
  have dp : (0:ℚ)<dust c b:=by exact_mod_cast dust_pos c b
  have tgt := mul_right_cancel₀ dp.ne' clr
  have eq : score f g (exactX c) (exactY c)=score f g (x' c b) (y' c b):=by
    rw [actual,tgt];push_cast;rfl
  dsimp [score] at eq
  simp only [Fin.prod_univ_three] at eq
  simp [change,otherX,otherY,others,inc,exactX,exactY,x',y'] at *
  linarith only [eq]

theorem other_bounds (c : Family) (b : Fin 3→Option Bool) (i : Fin 3) :
    1≤otherX c b i ∧ 0≤otherY c b i ∧ otherY c b i≤1 := by
  have loc (j : Fin 3) (mode) := ranges (c.prime j) (c.positive j) mode
  have one (j : Fin 3) (mode) : yy' (c.p j) (c.e j) mode≤1 := (loc j mode).2.2.2.trans
    ((div_le_iff₀ (by positivity)).mpr (by
      have e : (1:ℚ)≤c.e j:=by exact_mod_cast c.positive j
      linarith))
  have box (j l : Fin 3) (v w : Option Bool) :
    1≤xx' (c.p j) (c.e j) v*xx' (c.p l) (c.e l) w ∧
    0≤yy' (c.p j) (c.e j) v*yy' (c.p l) (c.e l) w ∧
    yy' (c.p j) (c.e j) v*yy' (c.p l) (c.e l) w≤1 :=
      ⟨one_le_mul_of_one_le_of_one_le (loc j v).1 (loc l w).1,
       mul_nonneg (loc j v).2.2.1 (loc l w).2.2.1,mul_le_one₀ (one j v) (loc l w).2.2.1 (one l w)⟩
  fin_cases i
  · exact box 1 2 none (b 2)
  · exact box 0 2 (b 0) (b 2)
  · exact box 0 1 none none

theorem shortY (c : Family) (b : Fin 3→Option Bool) (long : c.e 1+1=c.L)
    {i : Fin 3} (short : i≠1) : otherY c b i*c.L≤2 := by
  have range0 (j : Fin 3) (m) := ranges (c.prime j) (c.positive j) m
  have one j m : yy' (c.p j) (c.e j) m≤1:=(range0 j m).2.2.2.trans
    ((div_le_iff₀ (by positivity)).mpr (by
      have ep : (1:ℚ)≤c.e j:=by exact_mod_cast c.positive j
      linarith))
  have up := (le_div_iff₀ (by positivity)).mp (range0 1 none).2.2.2
  have L : (c.L:ℚ)=c.e 1+1:=by exact_mod_cast long.symm
  rw [←L] at up
  have go j m : (yy' (c.p 1) (c.e 1) none*yy' (c.p j) (c.e j) m)*c.L≤2 := by
    have h:=mul_le_mul_of_nonneg_left (one j m) (range0 1 none).2.2.1
    exact (mul_le_mul_of_nonneg_right (by simpa using h) (Nat.cast_nonneg c.L)).trans up
  by_cases zero : i=0
  · subst i;exact go 2 (b 2)
  · have two:i=2:=by omega
    subst i
    simpa [otherY,others,y',exactY,yy',mul_comm] using go 0 none

theorem short_nonneg (c : Family) (b : Fin 3→Option Bool) {f g : ℕ} (gp : 0<g) (fg : c.k*g≤f)
    (long : c.e 1+1=c.L) (bound : ∀i,b i=some true → c.p i≤c.L) {i : Fin 3} (short : i≠1) :
    0≤change c b f g i ∧ (b i≠none → 0<change c b f g i) := by
  have v:=other_bounds c b i
  have fp : 0<f:=(Nat.mul_pos (by have:=c.kp;omega) gp).trans_le fg
  cases mode:b i with
  | none=>simp [change,mode,exact_inc]
  | some tag=>
    have positive : 0<change c b f g i := by
      cases tag
      · have h:=dropped (f:=f) (g:=g) (c.prime i) (c.positive i) v.1 v.2.1
        change 0< inc _ _ _ _ _ _ _
        rw [mode]
        exact (by have:=(c.prime i).pos;positivity : (0:ℚ)<f/(2*(c.p i:ℚ))).trans_le h
      · have h:=retained_gain (g:=g) (c.prime i) c.kp fg (bound i mode) (c.cap i) v.1 v.2.1 (shortY c b long short)
        change 0< inc _ _ _ _ _ _ _
        rw [mode]
        have lm:=c.cap i
        have cp:=(c.prime i).pos
        have lp : 0<c.L:=by omega
        exact (by positivity : (0:ℚ)<g/((c.L:ℚ)^3*(c.p i:ℚ)^(c.e i))).trans_le h
    exact ⟨positive.le,fun _=>positive⟩

end OMA.MiddleOrder245212

end

section

/- A retained short right-hand power cannot offset the loss at the unique
long coordinate, whether the middle base is larger or smaller than sqrt L. -/
namespace OMA.MiddlePower245212
open Nat

theorem left {L q a b : ℕ} (qp : 2≤q) (head : L^6 < q^b) (sep : 2*a≤b) :
    L^3*q^a<q^b := by
  apply (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
  calc
    (L^3*q^a)^2 = L^6*q^(2*a) := by rw [mul_pow,←pow_mul,←pow_mul,mul_comm a 2]
    _ < q^b*q^b := Nat.mul_lt_mul_of_lt_of_le head (Nat.pow_le_pow_right (by omega) sep) (pow_pos (by omega) _)
    _ = (q^b)^2 := (sq _).symm

theorem right {k L q r b d : ℕ} (k0 : 256≤k) (q0 : 2≤q) (rb : r≤L)
    (slope : k*(d+1)<4*q) (sep : 16*(d+1)<b+1) (long : b+1=L) :
    L^3*r^d<q^b := by
  have qp : 1≤q:=by omega
  have high : L^3*r^d≤L^(d+3):=by
    rw [pow_add,mul_comm (L^d)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left rb d)
  apply high.trans_lt
  by_cases near : L≤q^2
  · calc
      _ ≤ (q^2)^(d+3) := Nat.pow_le_pow_left near _
      _ = q^(2*(d+3)) := (pow_mul ..).symm
      _ < _ := Nat.pow_lt_pow_right (by omega) (by omega)
  · have qle : 4*(d+4)≤q:=by
      have := Nat.mul_le_mul_right (d+1) k0
      omega
    have h0 : 16*((d+3)+1)^2≤L:=by
      have h:=Nat.pow_le_pow_left qle 2
      nlinarith only [h,Nat.lt_of_not_ge near]
    have grow := OMA.ComplementarySize245212.absorb (b:=L) (d:=d+3) h0
    apply (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2≠0)).mp
    calc
      _ = L^(2*(d+3)):=by rw [mul_comm 2 (d+3),pow_mul]
      _ ≤ 2^L:=grow
      _ ≤ q^L:=Nat.pow_le_pow_left q0 _
      _ < q^(b*2):=Nat.pow_lt_pow_right (by omega) (by omega)
      _ = _ := pow_mul .. 

end OMA.MiddlePower245212

end

section

/- The only possible mixed score has an exact left power, a retained
middle base, and a discarded right base. -/
namespace OMA.MiddleModes245212
open Nat Finset OMA.SingleMovingGap245212 OMA.TwoTallLocal245212
open OMA.MiddleChange245212 (inc)
open OMA.MiddleOrder245212

private theorem risk {c : Family} {b : Fin 3→Option Bool} {f g : ℕ} (gp : 0<g) (fg : c.k*g≤f)
    (negative : (f:ℚ)*otherX c b 1 < (g:ℚ)*((c.p 1:ℚ)-1)*otherY c b 1) :
    c.k*(c.e 2+1)<4*c.p 1 := by
  let u:ℚ:=(c.p 1:ℚ)-1
  have v:=other_bounds c b 1
  have fk : (c.k:ℚ)*g≤f:=by exact_mod_cast fg
  have g0 : (0:ℚ)<g:=by exact_mod_cast gp
  have lim : (c.k:ℚ)<u*otherY c b 1 := by
    apply lt_of_mul_lt_mul_right (a:=(g:ℚ)) _ g0.le
    nlinarith only [negative,mul_le_mul_of_nonneg_left v.1 (Nat.cast_nonneg (α:=ℚ) f),fk]
  have range0 j := ranges (c.prime j) (c.positive j) (b j)
  have one : y' c b 0≤1:=(range0 0).2.2.2.trans ((div_le_iff₀ (by positivity)).mpr (by
    have ep : (1:ℚ)≤c.e 0:=by exact_mod_cast c.positive 0
    linarith))
  have up := (le_div_iff₀ (by positivity)).mp (range0 2).2.2.2
  change y' c b 2*((c.e 2:ℚ)+1)≤2 at up
  have prod : otherY c b 1*((c.e 2:ℚ)+1)≤2 := by
    change (y' c b 0*y' c b 2)*_≤2
    have z:=mul_le_mul_of_nonneg_right one (range0 2).2.2.1
    change y' c b 0*y' c b 2≤1*y' c b 2 at z
    nlinarith only [up,mul_le_mul_of_nonneg_right z (by positivity : 0≤(c.e 2:ℚ)+1)]
  have pp := c.prime 1
  have pos : (1:ℚ)<c.p 1:=by exact_mod_cast pp.one_lt
  have pp' : (0:ℚ)≤u:=by dsimp [u];linarith
  exact_mod_cast (show (c.k:ℚ)*((c.e 2:ℚ)+1)<4*(c.p 1:ℚ) by
    have w := mul_lt_mul_of_pos_right lim (by positivity : 0<(c.e 2:ℚ)+1)
    have h:=mul_le_mul_of_nonneg_left prod pp'
    dsimp [u] at w h; nlinarith only [w,h,pos])

theorem force (c : Family) (b : Fin 3→Option Bool) {f g Q : ℕ} (gp : 0<g) (fg : c.k*g≤f)
    (long : c.e 1+1=c.L) (k0 : 256≤c.k) (smallK : c.k+1≤c.L)
    (pq : c.p 0<c.p 1) (sep0 : 2*c.e 0≤c.e 1) (sep2 : 16*(c.e 2+1)<c.e 1+1)
    (power : c.L^6<c.p 1^c.e 1) (cut :Q<c.p 1^c.e 1) (cover : c.L≤Q)
    (rule : ∀i,b i=if c.p i^c.e i≤Q then none else some (decide (c.p i≤Q)))
    (notboth : ¬(b 0=none ∧ b 2=none))
    (small : ∀i,b i=some true → c.p i≤ max (c.k+1) c.L)
    (hit : (f+g)*dust c b=f*NX c b+g*NY c b)
    (actual : score f g (exactX c) (exactY c)=(f+g:ℕ)) :
    b 0=none ∧ b 1=some true ∧ b 2=some false ∧
    (f:ℚ)*(x' c b 0*x' c b 2)<(g:ℚ)*((c.p 1:ℚ)-1)*(y' c b 0*y' c b 2) := by
  have bounds (i : Fin 3) (h : b i=some true) : c.p i≤c.L:=by simpa [max_eq_right smallK] using small i h
  have nonneg {i : Fin 3} (sh : i≠1) := short_nonneg c b gp fg long bounds sh
  have short0:=nonneg (i:=0) (by decide)
  have short2:=nonneg (i:=2) (by decide)
  have total:=zero_sum c b f g hit actual
  have one : b 1=some true := by
    have sm : b 1=some (decide (c.p 1≤Q)):=by simpa [cut.not_ge] using rule 1
    by_contra no
    have mode : b 1=some false := by simpa [sm] using (show decide (c.p 1≤Q)=false by cases tag:decide (c.p 1≤Q) <;> simp_all)
    have v:=other_bounds c b 1
    have plus:=OMA.MiddleChange245212.dropped (f:=f) (g:=g) (c.prime 1) (c.positive 1) v.1 v.2.1
    have ne : 0<change c b f g 1:=by
      dsimp only [change];rw [mode]
      have fp : 0<f:=(Nat.mul_pos (by omega : 0<c.k) gp).trans_le fg
      have pp:=(c.prime 1).pos
      exact (show (0:ℚ)<f/(2*(c.p 1:ℚ)) by positivity).trans_le plus
    linarith only [ne,short0.1,short2.1,total]
  have qcap := bounds 1 one
  have minus : change c b f g 1<0 := by
    by_cases a : b 0=none
    · have ne : b 2≠none:=fun h=>notboth ⟨a,h⟩
      linarith only [short0.1,short2.2 ne,total]
    · linarith only [short0.2 a,short2.1,total]
  have positive : (f:ℚ)*otherX c b 1<(g:ℚ)*((c.p 1:ℚ)-1)*otherY c b 1 := by
    dsimp only [change] at minus;rw [one,OMA.MiddleChange245212.retained (c.prime 1)] at minus
    have pp : (1:ℚ)<c.p 1:=by exact_mod_cast (c.prime 1).one_lt
    by_contra! bad
    exact (not_lt_of_ge (div_nonneg (sub_nonneg.mpr bad) (by positivity))) minus
  have sr:=risk gp fg positive
  have v:=other_bounds c b 1
  have cost : -((g:ℚ)/(c.p 1:ℚ)^(c.e 1)) ≤ change c b f g 1 := by
    dsimp only [change];rw [one]
    simpa only [neg_div] using OMA.MiddleChange245212.retained_loss (f:=f) (g:=g)
      (c.prime 1) (e:=c.e 1) (zero_le_one.trans v.1) v.2.2
  have cannot {i : Fin 3} (short : i≠1) (pow : c.L^3*c.p i^c.e i<c.p 1^c.e 1)
      (opp : 0≤change c b f g (if i=0 then 2 else 0)) : b i≠some true := by
    intro mode
    have v:=other_bounds c b i
    have gain:=OMA.MiddleChange245212.retained_gain (c.prime i) c.kp fg (bounds i mode) (c.cap i)
      v.1 v.2.1 (shortY c b long short)
    have strict : (g:ℚ)/(c.p 1:ℚ)^(c.e 1)<change c b f g i := by
      dsimp only [change];rw [mode]
      apply lt_of_lt_of_le _ gain
      have lp : 0<c.L:=by omega
      have pp:=(c.prime i).pos
      exact div_lt_div_of_pos_left (by exact_mod_cast gp) (by positivity) (by exact_mod_cast pow)
    by_cases i0 : i=0
    · subst i;change 0≤change c b f g 2 at opp
      linarith only [strict,cost,opp,total]
    · have i2:i=2:=by omega
      subst i;simp at opp
      linarith only [strict,cost,opp,total]
  have leftPow : c.L^3*c.p 0^c.e 0<c.p 1^c.e 1 := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pq.le _)).trans_lt
    (OMA.MiddlePower245212.left (c.prime 1).two_le power sep0)
  have leftNo:=cannot (i:=0) (by decide) leftPow (by exact short2.1)
  have zero : b 0=none:=by
    by_contra no
    have cap0 : c.p 0≤Q:=pq.le.trans (qcap.trans cover)
    by_cases small : c.p 0^c.e 0≤Q
    · exact no (by simpa [small] using rule 0)
    · exact leftNo (by simpa [small,cap0] using rule 0)
  have two : b 2=some false := by
    have ne : b 2≠none:=fun h=>notboth ⟨zero,h⟩
    cases h:b 2 with
    | none=>contradiction
    | some tag=>
      cases tag with
      | false=>rfl
      | true=>
        have pow:=OMA.MiddlePower245212.right k0 (c.prime 1).two_le (bounds 2 h) sr sep2 long
        exact False.elim (cannot (i:=2) (by decide) pow (by exact short0.1) h)
  exact ⟨zero,one,two,positive⟩

end OMA.MiddleModes245212

end

section

/- An absolute harmonic bound on the least prime, independent of which
coordinate carries the longest exponent. -/
namespace OMA.MiddleLeast245212
open Nat Finset OMA.TwoTallLocal245212 OMA.SingleMovingGap245212
open OMA.LeastTallFactor245212 (localY)
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.LeastTallFactor245212 (localX)
open OMA.SingleMovingOriginal245212 (identities)

theorem bound (c : Family) {v : Fin 3} (long : c.e v+1=c.L)
    (least : ∀i,c.p 0≤c.p i) (large : 33≤c.p 0) (tall : 32≤c.L)
    (actual : score (F c.k) (G c.k) (exactX c) (exactY c)=(F c.k+G c.k:ℕ)) :
    c.p 0≤4*(c.k+1) := by
  let f:=F c.k
  let g:=G c.k
  let P:=∏i,exactX c i
  let S:=∏i,exactY c i
  let u:ℚ:=(c.p 0:ℚ)-1
  have loc i := OMA.LeastTallFactor245212.localX large (least i) (c.prime i) (c.positive i)
  change ∀i, 1≤exactX c i ∧ exactX c i≤33/32 ∧ u*(exactX c i-1)≤1 at loc
  have p0 i := (zero_le_one.trans (loc i).1)
  have Xprod : u*(P-1) ≤ 13/4 := by
    let x:=exactX c
    have a:=mul_le_mul_of_nonneg_right (loc 0).2.2 (mul_nonneg (p0 1) (p0 2))
    have b:=mul_le_mul_of_nonneg_right (loc 1).2.2 (p0 2)
    have d:=mul_le_mul (loc 1).2.1 (loc 2).2.1 (p0 2) (by norm_num : (0:ℚ)≤33/32)
    dsimp only [P];rw [Fin.prod_univ_three]
    nlinarith only [a,b,d,(loc 2).2.2,(loc 2).2.1]
  have nonY i : 0≤exactY c i := (ranges (c.prime i) (c.positive i) none).2.2.1
  have bound i : exactY c i≤1 := (localY (c.prime i) (c.positive i) (large.trans (least i)) none).trans (by norm_num)
  have s := (ranges (c.prime v) (c.positive v) none).2.2.2
  change exactY c v≤2/((c.e v:ℚ)+1) at s
  have T : (32:ℚ)≤(c.e v:ℚ)+1:=by exact_mod_cast (long ▸ tall : 32≤c.e v+1)
  have lowS : S≤1/16 := by
    calc
      _ = (∏ i∈univ.erase v,exactY c i)*exactY c v := (prod_erase_mul _ _ (mem_univ v)).symm
      _ ≤ exactY c v := mul_le_of_le_one_left (nonY v) (prod_le_one (fun j _=>nonY j) (fun j _=>bound j))
      _ ≤ _ := s.trans ((div_le_iff₀ (by positivity)).mpr (by linarith only [T]))
  change (f:ℚ)*P+(g:ℚ)*S=(f+g:ℕ) at actual
  push_cast at actual

  have old:=OMA.SingleMovingOriginal245212.identities c.k
  have k0:=Nat.two_pow_pos c.k
  have gm : c.k+1≤g:=by
    dsimp [g,G];rw [pow_succ]
    have z : c.k+1≤2^c.k:=Nat.lt_pow_self (by decide)
    omega
  have fg : (f:ℚ)≤((c.k:ℚ)+1)*g:=by
    exact_mod_cast (show f≤(c.k+1)*g by
      dsimp [f,g];rw [old.2.2,Nat.add_mul,one_mul];exact Nat.add_le_add_left gm _)
  have up : 0≤u:=by
    dsimp [u]
    have h : (33:ℚ)≤c.p 0:=by exact_mod_cast large
    linarith
  have g0 : (0:ℚ)<g:=by exact_mod_cast old.1
  have p1 : u*g ≤ 13/4*f+(1/16)*(u*g):=by
    nlinarith only [congrArg (fun z:ℚ=>z*u) actual,mul_le_mul_of_nonneg_right Xprod
      (Nat.cast_nonneg (α:=ℚ) f),mul_le_mul_of_nonneg_left lowS (mul_nonneg up g0.le)]
  by_contra! huge
  have hh : 4*((c.k:ℚ)+1)<c.p 0 := by exact_mod_cast huge
  have k8 : (8:ℚ)≤c.k:=by exact_mod_cast c.kp
  dsimp only [u] at p1
  nlinarith only [p1,fg,mul_lt_mul_of_pos_right hh g0,mul_le_mul_of_nonneg_right k8 g0.le,g0]

end OMA.MiddleLeast245212

end

section

/- With the least odd prime exact, the middle base retained, and the
last base dropped, the cleared three-factor score is an equation in the
two divisor moments of the exact prefix. Restoring the middle factor
with a negative sign selects the strict side of that equation. -/
namespace OMA.ThreeModeMiddleEquation245212
open Nat Finset ArithmeticFunction OMA.Smooth245212
open OMA.SingleMovingGap245212 OMA.TwoTallLocal245212 OMA.ThreeMovingLocal245212
open OMA.ThreeMovingOriginal245212 (F G)
open scoped ArithmeticFunction.sigma
open OMA.ComplementaryLocal245212 (binary)
open OMA.ThreeMovingOriginal245212 (identities)

private theorem prefixData (k p e : ℕ) (pr : p.Prime) (odd : Odd p) :
    let h:=2^k*p^e
    W h=F k*W (p^e) ∧ σ 1 h=G k*σ 1 (p^e) ∧
    2*h*(σ 0 h)=(F k+G k)*((e+1)*p^e) := by
  dsimp only
  have cop:=((Nat.coprime_two_left.mpr odd).pow_left k).pow_right e
  have sum : σ 1 (2^k)=G k := by
    dsimp [G];zify [Nat.cast_sub (show 1≤2^(k+1) from Nat.two_pow_pos _)]
    exact (OMA.ComplementaryLocal245212.binary k).1
  have weight : W (2^k)=F k := by exact_mod_cast (OMA.ComplementaryLocal245212.binary k).2
  rw [w_mult.map_mul_of_coprime cop,isMultiplicative_sigma.map_mul_of_coprime cop,
    isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow Nat.prime_two,
    sigma_zero_apply_prime_pow pr,sum,weight,(OMA.ThreeMovingOriginal245212.identities k).2.1,pow_succ]
  exact ⟨rfl,rfl,by ring⟩

theorem adapter (c : Family) (odd : Odd (c.p 0)) (b : Fin 3→Option Bool)
    (b0 : b 0=none) (b1 : b 1=some true) (b2 : b 2=some false)
    (hit : (F c.k+G c.k)*dust c b=F c.k*NX c b+G c.k*NY c b)
    (negative : (F c.k:ℚ)*(x' c b 0*x' c b 2)<
      (G c.k:ℚ)*((c.p 1:ℚ)-1)*(y' c b 0*y' c b 2)) :
    let h:=2^c.k*(c.p 0)^(c.e 0)
    let A:=W h;let S:=σ 1 h;let H:=2*h*(σ 0 h)
    let B:=c.e 1+1;let C:=c.e 2+1;let u:=c.p 1-1
    H*B*C*u^2=c.p 1*(A*C*(B*u-1)+S*u) ∧ A*C<S*u := by
  dsimp only
  obtain ⟨av,sv,hv⟩:=prefixData c.k (c.p 0) (c.e 0) (c.prime 0) odd
  rw [av,sv,hv]
  constructor
  · simp only [dust,NX,NY,Fin.prod_univ_three,b0,b1,b2,Dn,Nx,Ny,den,xn,yn,
      if_true,Bool.false_eq_true,if_false,mul_one] at hit
    linear_combination hit
  · let D i:=Dn (c.p i) (c.e i) (b i)
    have dp (i:Fin 3) : 0 < (D i:ℚ):= by exact_mod_cast Dpos (c.prime i) (c.e i) (b i)
    have wx (i:Fin 3) : x' c b i*(D i:ℚ)=Nx (c.p i) (c.e i) (b i) :=
      (moments (c.prime i) (c.e i) (b i)).1
    have sy (i:Fin 3) : y' c b i*(D i:ℚ)=Ny (c.p i) (c.e i) (b i) :=
      (moments (c.prime i) (c.e i) (b i)).2
    have scale:=mul_lt_mul_of_pos_right negative (mul_pos (dp 0) (dp 2))
    have ex : (x' c b 0*x' c b 2)*((D 0:ℚ)*D 2)=
        Nx (c.p 0) (c.e 0) (b 0)*(Nx (c.p 2) (c.e 2) (b 2):ℚ) := by
      rw [←wx 0,←wx 2];ring
    have ey : (y' c b 0*y' c b 2)*((D 0:ℚ)*D 2)=
        Ny (c.p 0) (c.e 0) (b 0)*(Ny (c.p 2) (c.e 2) (b 2):ℚ) := by
      rw [←sy 0,←sy 2];ring
    rw [mul_assoc (F c.k:ℚ),mul_assoc ((G c.k:ℚ)*_),ex,ey] at scale
    simp only [b0,b2,Nx,Ny,xn,yn,Bool.false_eq_true,if_false,Nat.cast_one,mul_one] at scale
    have pos:=(c.prime 1).pos
    rw [←Nat.cast_one (R:=ℚ),←Nat.cast_sub pos] at scale
    exact_mod_cast (by linarith only [scale] :
      (F c.k:ℚ)*W (c.p 0^c.e 0)*(c.e 2+1:ℕ) <
        (G c.k:ℚ)*σ 1 (c.p 0^c.e 0)*(c.p 1-1:ℕ))

end OMA.ThreeModeMiddleEquation245212

end

section

/- Transfer from the seven sorted integer parameters of the original equation
to the exact cofactor equation, with polynomial height independent of every prime. -/
namespace OMA.MiddleBridge245212
open Nat Finset ArithmeticFunction OMA.SingleMovingGap245212
open OMA.ThreeMovingOriginal245212 (F G)
open OMA.SingleMovingStep245212 (degree)
open OMA.SingleMovingHeight245212 (constant)
open OMA.Smooth245212 (total W)
open OMA.SingleMovingOriginal245212 (identities)
open scoped ArithmeticFunction.sigma

def output (D k p q a b d : ℕ) : Prop :=
  let h:=2^k*p^a
  let A:=W h;let S:=σ 1 h;let H:=2*h*(σ 0 h)
  let B:=b+1;let C:=d+1;let u:=q-1
  p≤4*(k+1) ∧ h≤(B+1)^D ∧ H*B*C*u^2=q*(A*C*(B*u-1)+S*u) ∧ A*C<S*u

theorem escape {C E k p q r a b d : ℕ} (dyadic : 2^k≤C*((b+1)+1)^E)
    (high : OMA.MiddleCut245212.cutoff C E degree≤b+1)
    (pp : p.Prime) (qp : q.Prime) (rp : r.Prime) (p33 : 33≤p) (pq : p<q) (qr : q<r)
    (ap : 0<a) (bp : 0<b) (dp : 0<d) (k0 : 256≤k)
    (left : 16*(a+1)<b+1) (right : 16*(d+1)<b+1)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    output (OMA.MiddleCut245212.exponent E degree) k p q a b d := by
  let P : Fin 3→ℕ:=![p,q,r]
  let E' : Fin 3→ℕ:=![a,b,d]
  have pm i : (P i).Prime:=by fin_cases i <;> simp [P,pp,qp,rp]
  have od i : Odd (P i):=by
    apply (pm _).odd_of_ne_two
    fin_cases i <;> simp [P] <;> omega
  have inj : P.Injective:=by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have pos i : 0<E' i:=by fin_cases i <;> simp [E'] <;> omega
  let L:=b+1
  have lens i : E' i+1≤L:=by fin_cases i <;> simp [E',L] <;> omega
  let c : Family:=⟨P,E',k,L,pm,pos,by omega,⟨1,rfl⟩,lens,inj⟩
  let x:=OMA.MiddleCut245212.scale k L
  let f:=F k
  let g:=G k
  have kd:=OMA.SingleMovingOriginal245212.identities k
  have repr : 2^k*total P E'=2^k*p^a*q^b*r^d := by simp [total,Fin.prod_univ_three,P,E',mul_assoc]
  have actual:=OMA.SingleMovingOriginal245212.physical c k od inj (by rw [show 2^k*total c.p c.e=2^k*p^a*q^b*r^d from repr];exact eqn)
  have D0 : 1≤degree:=by decide
  obtain ⟨kL,dyad,xL,x128,pow⟩:=OMA.MiddleCut245212.power D0 dyadic high (rfl : b+1=L) qp.two_le
  have xfg : f+g≤x:=by
    dsimp only [x,OMA.MiddleCut245212.scale,f,g]
    nlinarith only [Nat.zero_le L,Nat.zero_le (F k+G k),Nat.zero_le ((F k+G k)*L)]
  obtain ⟨bits,Q,xQ,Qmax,rule,hit⟩:=OMA.MiddleWitness245212.witness c f g x x128 xfg xL actual
  have noalt : ¬(bits 0=none ∧ bits 2=none):=by
    rintro ⟨z,t⟩
    have extract (j) (h : bits j=none) : c.p j^c.e j≤Q := by
      by_contra no
      have v:=rule j
      simp [h,no] at v
    exact OMA.MiddleCut245212.not_both pp qp rp (od 1) pq qr bp D0 (by omega) dyad Qmax pow eqn
      ⟨extract 0 z,extract 2 t⟩
  have sm i : ¬c.p i∣2^(k+1):=by
    intro div
    have t:=(c.prime i).dvd_of_dvd_pow div
    have pr : c.p i≠2:=by obtain ⟨t,et⟩:=od i; change P i≠2; omega
    exact pr ((Nat.prime_dvd_prime_iff_eq (c.prime i) Nat.prime_two).mp t)
  have modes:=OMA.MiddleModes245212.force c bits kd.1 (by change k*G k≤F k;rw [kd.2.2];exact Nat.le_add_right _ _)
    rfl k0 kL pq (by change 2*a≤b;omega) right
    (by change L^6<q^b;exact (Nat.pow_le_pow_left xL 6).trans_lt
          ((Nat.pow_le_pow_right (by omega : 1≤x) (by omega : 6≤20*degree)).trans_lt pow))
    (Qmax.trans_lt ((Nat.pow_le_pow_right (by omega : 1≤x) (by omega : degree≤20*degree)).trans_lt pow))
    (xL.trans xQ) rule noalt (retained kd.2.1 sm hit) hit actual
  obtain ⟨m0,m1,m2,sgn⟩:=modes
  have eqm:=OMA.ThreeModeMiddleEquation245212.adapter c (od 0) bits m0 m1 m2 hit sgn
  have lp : ∀i,c.p 0≤c.p i:=by intro i;fin_cases i <;> change p≤_ <;> first | exact le_rfl | exact pq.le | exact (pq.trans qr).le
  have LB : 32≤L:=by
    have t : 512≤OMA.MiddleCut245212.cutoff C E degree :=by
      unfold OMA.MiddleCut245212.cutoff;omega
    omega
  have pB:=OMA.MiddleLeast245212.bound c (v:=1) rfl lp p33 LB actual
  have xp : p^a≤Q:=by
    by_contra off
    have no:c.p 0^c.e 0>Q:=Nat.lt_of_not_ge off
    have w:=rule 0
    rw [m0,if_neg no.not_ge] at w
    cases w
  exact ⟨pB,OMA.MiddleCut245212.size high dyadic _ (xp.trans Qmax),eqm⟩

def threshold := OMA.MiddleCut245212.cutoff (constant degree) (2*degree) degree
def exponent := OMA.MiddleCut245212.exponent (2*degree) degree

theorem original {k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p33 : 33≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (k0 : 256≤k) (high : threshold≤b+1)
    (left : 16*(a+1)<b+1) (right : 16*(d+1)<b+1)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    output exponent k p q a b d := by
  apply escape _ high pp qp rp p33 pq qr ap bp dp k0 left right eqn
  let P : Fin 3→ℕ:=![p,q,r]
  let E : Fin 3→ℕ:=![a,b,d]
  have pm i : (P i).Prime:=by fin_cases i <;> simp [P,pp,qp,rp]
  have od i : Odd (P i):=by apply (pm _).odd_of_ne_two;fin_cases i <;> simp [P] <;> omega
  have inj : P.Injective:=by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have pos i : 0<E i:=by fin_cases i <;> simp [E] <;> omega
  have repr : 2^k*total P E=2^k*p^a*q^b*r^d := by simp [total,Fin.prod_univ_three,P,E,mul_assoc]
  exact OMA.SingleMovingHeight245212.original k (b+1) P E pm od inj pos ⟨1,rfl⟩
    (fun i=>by fin_cases i <;> simp [E] <;> omega) (by rw [repr];exact eqn)

end OMA.MiddleBridge245212

end


/- Absolute finiteness of the three-odd-prime sector -/

section

/- A positive integral gap below a rectangular bilinear form cannot be
arbitrarily small relative to the product of its two variables. Neither
variable nor the coefficient of their product enters the gap multiplier. -/
namespace OMA.PositiveBilinearGap245212

def cost (I J K : ℕ) := (4*(I+J+K+1)+1)^3

private theorem short {C Z P G I J K N : ℕ} (gp : 0<G)
    (eqn : C*Z*P=G+I*Z+J*P+K) (zle : Z≤N) (ile : I≤N) (kle : K+1≤N) :
    Z*P≤(N+1)^3*G := by
  have pos : J<C*Z:=by
    by_contra! no
    have :=Nat.mul_le_mul_right P no
    omega
  have mul := Nat.mul_le_mul_right P (Nat.succ_le_of_lt pos)
  have small : P≤G+(I*Z+K):=by nlinarith only [mul,eqn]
  have kg := Nat.mul_le_mul_left (I*Z+K) (show 1≤G from gp)
  have cut : P≤(I*Z+K+1)*G:=by nlinarith only [small,kg]
  have lim : I*Z+K+1≤(N+1)^2:=by
    have :=Nat.mul_le_mul ile zle
    nlinarith only [this,kle,Nat.zero_le N]
  calc
    _ ≤ (N+1)*((N+1)^2*G) := Nat.mul_le_mul (by omega) (cut.trans (Nat.mul_le_mul_right G lim))
    _ = _ := by ring

theorem gap {C Z P G I J K : ℕ} (gp : 0<G) (eqn : C*Z*P=G+I*Z+J*P+K) :
    Z*P≤cost I J K*G := by
  let h:=I+J+K+1
  have hi : I≤h:=by dsimp [h];omega
  have hj : J≤h:=by dsimp [h];omega
  have hk : K+1≤h:=by dsimp [h];omega
  change Z*P≤(4*h+1)^3*G
  by_cases sz : Z≤4*h
  · exact short gp eqn sz (by omega) (by omega)
  by_cases sp : P≤4*h
  · have e : C*P*Z=G+J*P+I*Z+K:=by nlinarith only [eqn]
    simpa only [Nat.mul_comm P Z] using short gp e sp (by omega) (by omega)
  have iz:=Nat.mul_le_mul_left Z (show 4*I≤P by omega)
  have jp:=Nat.mul_le_mul_left P (show 4*J≤Z by omega)
  have zp : 0<Z:=by omega
  have pk:=Nat.le_mul_of_pos_left P zp
  have kp : 4*K≤Z*P:=by omega
  have cp : 0<C:=by by_contra! zero;rw [Nat.eq_zero_of_le_zero zero] at eqn;simp at eqn;omega
  have large:=Nat.mul_le_mul_right (Z*P) (show 1≤C from cp)
  have four : Z*P≤4*G:=by nlinarith only [eqn,iz,jp,kp,large]
  have top : 4≤(4*h+1)^3:=by
    have nh : 1≤h:=by omega
    exact (by decide : 4≤5^3).trans (Nat.pow_le_pow_left (by omega) _)
  exact four.trans (Nat.mul_le_mul_right G top)

end OMA.PositiveBilinearGap245212

end

section

/- A one-sided separation bound for the exact cofactor of the small odd
prime. It is polynomial in its parameters, even if both powers are huge. -/
namespace OMA.MiddlePoleGap245212
open OMA.PositiveBilinearGap245212

theorem relative {k g Z P L M H A U V R : ℕ} (zp : 0<Z) (pp : 0<P) (lp : 0<L)
    (h : H=M*Z*P) (a : L*A=(k*Z+1)*(g*P+1)) (rp : 0<R) (diff : V*A+R=U*H) :
    H≤M*L*cost (V*k) (V*g) V*R := by
  let C:=U*M*L-V*k*g
  have full : U*M*L*(Z*P)=V*k*g*(Z*P)+L*R+(V*k)*Z+(V*g)*P+V:=by
    nlinarith only [congrArg (L*·) diff,congrArg (V*·) a,congrArg ((U*L)*·) h]
  have left : V*k*g*(Z*P)≤U*M*L*(Z*P):=by omega
  have low:=Nat.le_of_mul_le_mul_right left (Nat.mul_pos zp pp)
  have key:=Nat.sub_add_cancel low
  have core : C*Z*P=L*R+(V*k)*Z+(V*g)*P+V:=by
    dsimp only [C]
    nlinarith only [full,congrArg (·*(Z*P)) key]
  have gap:=OMA.PositiveBilinearGap245212.gap (Nat.mul_pos lp rp) core
  rw [h]
  simpa only [mul_assoc,mul_comm,mul_left_comm] using Nat.mul_le_mul_left M gap

private theorem scale {q k g : ℕ} (qp : 0<q) :
    cost (q*k) (q*g) q≤q^3*cost k g 1 := by
  unfold cost
  rw [←mul_pow]
  apply Nat.pow_le_pow_left
  nlinarith only [show 1≤q from qp]

/-- If the middle-prime asymptotic moment hits exactly, its exponent
length is bounded without using the middle prime or either large power. -/
theorem mixed {k g Z P L M H A S u q B C : ℕ} (zp : 0<Z) (pp : 0<P) (lp : 0<L)
    (mh : H=M*Z*P) (ma : L*A=(k*Z+1)*(g*P+1)) (up : 0<u) (qu : q=u+1)
    (cp : 0<C) (bp : 0<B) (ss : S≤H) (positive : C*A<u*S)
    (hit : H*B*C*u^2=q*(A*C*(B*u-1)+S*u)) :
    let K:=M*L*cost k g 1
    B≤16*K^5 := by
  let K:=M*L*cost k g 1
  let E:=H*u-A*q
  let Δ:=H-A
  have qp : 0<q:=by omega
  have bu:=Nat.sub_add_cancel (show 1≤B*u from Nat.mul_pos bp up)
  have raw : B*u*C*(H*u)+q*(A*C)=B*u*C*(A*q)+q*(u*S):=by
    nlinarith only [hit,congrArg (fun z : ℕ=>q*(A*C)*z) bu]
  have strict : A*q<H*u:=by
    by_contra! no
    have small:=Nat.mul_le_mul_left (B*u*C) no
    have sign:=Nat.mul_lt_mul_of_pos_left positive qp
    nlinarith only [raw,small,sign]
  have ep : 0<E:=Nat.sub_pos_of_lt strict
  have ee : q*A+E=u*H:=by
    rw [Nat.mul_comm q A,Nat.mul_comm u H,Nat.add_comm]
    exact Nat.sub_add_cancel strict.le
  have ah : A<H:=by
    by_contra! no
    have bad:=Nat.mul_le_mul_right u no
    rw [qu,Nat.mul_add,Nat.mul_one] at strict
    omega
  have dp : 0<Δ:=Nat.sub_pos_of_lt ah
  have de : 1*A+Δ=1*H:=by dsimp [Δ];omega
  have small : H≤K*Δ:=by
    simpa only [one_mul] using relative zp pp lp mh ma dp de
  have kp : 0<K:=by
    by_contra! no
    have zero : K=0:=by omega
    rw [zero,zero_mul] at small
    omega
  have sb : B*E≤q*H:=by
    have prod : B*u*C*E+q*(A*C)=q*(u*S):=by
      nlinarith only [raw,congrArg (fun z : ℕ=>B*u*C*z) ee]
    have main : (B*E*C)*u≤(q*S)*u:=by nlinarith only [prod,Nat.zero_le (q*(A*C))]
    have bare:=Nat.le_of_mul_le_mul_right main up
    exact (Nat.le_mul_of_pos_right _ cp).trans (bare.trans (Nat.mul_le_mul_left q ss))
  have iden : q*Δ=E+H:=by
    simp only [one_mul] at de
    nlinarith only [ee,congrArg (q*·) de,congrArg (·*H) qu]
  change B≤16*K^5
  by_cases large : 2*K≤q
  · have high:=Nat.mul_le_mul_right Δ large
    have two : q*Δ≤2*E:=by nlinarith only [high,iden,small]
    have chain : B*E≤(2*K)*E:=by
      calc
        B*E ≤ q*H := sb
        _ ≤ K*(q*Δ) := by simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left q small
        _ ≤ (2*K)*E := by simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left K two
    have bsmall:=Nat.le_of_mul_le_mul_right chain ep
    have pow : K≤K^5:=by simpa only [pow_one] using Nat.pow_le_pow_right kp (by decide : 1≤5)
    omega
  · have rel:=relative zp pp lp mh ma ep ee
    have cap : H≤q^3*K*E:=by
      exact rel.trans (by
        have s:=Nat.mul_le_mul_right E (Nat.mul_le_mul_left (M*L) (scale (k:=k) (g:=g) qp))
        simpa only [K,mul_comm,mul_left_comm,mul_assoc] using s)
    have tight : B*E≤(q^4*K)*E:=sb.trans (by
      calc
        q*H ≤ q*(q^3*K*E) := Nat.mul_le_mul_left q cap
        _ = _ := by ring)
    have bnd:=Nat.le_of_mul_le_mul_right tight ep
    calc
      B ≤ q^4*K := bnd
      _ ≤ (2*K)^4*K := Nat.mul_le_mul_right K (Nat.pow_le_pow_left (by omega) _)
      _ = 16*K^5 := by ring

end OMA.MiddlePoleGap245212

end

section

/- Instantiate the positive bilinear gap using the two exact weighted
moments of the dyadic factor and the smallest odd-prime power. -/
namespace OMA.MiddlePoleOriginal245212
open Nat ArithmeticFunction OMA.Smooth245212 OMA.PositiveBilinearGap245212
open scoped ArithmeticFunction.sigma
open OMA.DivisorHeight245212 (dyadic_moments)

def K (k p a : ℕ) :=
  (k+1)*(a+1)*(p-1)^2*cost k (p*((a+1)*(p-1)-1)) 1

theorem original {k p a q B C : ℕ} (pr : p.Prime) (op : Odd p) (qg : 2≤q)
    (bp : 0<B) (cp : 0<C)
    (positive :
      C*W (2^k*p^a)<(q-1)*σ 1 (2^k*p^a))
    (hit :
      (2*(2^k*p^a)*σ 0 (2^k*p^a))*B*C*(q-1)^2=
      q*(W (2^k*p^a)*C*(B*(q-1)-1)+(σ 1 (2^k*p^a))*(q-1))) :
    B≤16*(K k p a)^5 := by
  let Z:=2^(k+1)
  let P:=p^a
  let g:=p*((a+1)*(p-1)-1)
  let m:=2^k*p^a
  let H:=2*m*σ 0 m
  let A:=W m
  let M:=(k+1)*(a+1)
  have cop : (2^k).Coprime (p^a):=((Nat.coprime_two_left.mpr op).pow_left k).pow_right a
  have ph : 0<p-1:=Nat.sub_pos_of_lt pr.one_lt
  have base : 1≤(a+1)*(p-1):=Nat.mul_pos (Nat.succ_pos _) ph
  have h : H=M*Z*P:=by
    dsimp only [H,m,M,Z,P]
    rw [isMultiplicative_sigma.map_mul_of_coprime cop,sigma_zero_apply_prime_pow prime_two,
      sigma_zero_apply_prime_pow pr,pow_succ]
    ring
  have localW : (p-1)^2*W (p^a)=g*P+1:=by
    dsimp only [g,P]
    zify [Nat.cast_sub pr.pos,Nat.cast_sub base]
    exact (OMA.ComplementaryLocal245212.moments pr a).2
  have w : (p-1)^2*A=(k*Z+1)*(g*P+1):=by
    dsimp only [A,m]
    rw [w_mult.map_mul_of_coprime cop,(OMA.DivisorHeight245212.dyadic_moments k).1,←localW]
    dsimp only [Z]
    ring
  have bound : σ 1 m≤H:=by
    have le : σ 1 m ≤ m*σ 0 m:=by
      rw [sigma_one_apply,sigma_zero_apply]
      calc
        _ ≤ ∑ _ ∈ m.divisors,m := Finset.sum_le_sum (fun _ hd=>Nat.divisor_le hd)
        _ = _ := by simp [mul_comm]
    dsimp only [H]
    nlinarith only [le,Nat.zero_le (m*σ 0 m)]
  exact OMA.MiddlePoleGap245212.mixed (Nat.two_pow_pos _) (pow_pos pr.pos _)
    (pow_pos ph 2) h w (by omega : 0<q-1) (by omega : q=(q-1)+1) cp bp bound positive hit

end OMA.MiddlePoleOriginal245212

end

section

/- Close the mixed branch: logarithmically bounded small exponents can
never support an unbounded middle exponent. All bounds are Nat terms. -/
namespace OMA.MiddlePoleFinite245212
open OMA.PositiveBilinearGap245212 OMA.MiddlePoleOriginal245212

def cutoff (D : ℕ) :=
  let j:=82*D
  (8*(16*(j+1)^2+68+6*j))^81

theorem cost_bound {k p a : ℕ} (small : p≤32+4*(k+1)) :
    16*(K k p a)^5≤(8*(k+a+34))^81 := by
  let X:=8*(k+a+34)
  have big : 16≤X:=by dsimp [X];omega
  have xp : p≤X:=by dsimp [X];omega
  have xa : a+1≤X:=by dsimp [X];omega
  have xk : k+2≤X:=by dsimp [X];omega
  have xle : X≤X^3:=by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<X) (by decide : 1≤3)
  have xl : p-1≤X:=by omega
  have g : p*((a+1)*(p-1)-1)≤X^3:=calc
    _ ≤ X*(X*X) := Nat.mul_le_mul xp ((Nat.sub_le _ _).trans (Nat.mul_le_mul xa xl))
    _ = _ := by ring
  have coeff : 4*(k+p*((a+1)*(p-1)-1)+1+1)+1≤X^4:=by
    have nine:=Nat.mul_le_mul_right (X^3) (show 9≤X by omega)
    have pos:=Nat.one_le_pow 3 X (by omega)
    rw [pow_succ X 3]
    nlinarith only [xk,xle,g,nine,pos,Nat.zero_le (X^3)]
  have core : K k p a≤X^16:=by
    unfold K cost
    calc
      _ ≤ ((X*X)*X^2)*(X^4)^3 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) xa) (Nat.pow_le_pow_left xl _))
          (Nat.pow_le_pow_left coeff _)
      _ = _ := by rw [←pow_mul,←sq,←pow_add,←pow_add]
  change 16*(K k p a)^5≤X^81
  exact (Nat.mul_le_mul big (Nat.pow_le_pow_left core 5)).trans_eq
    (by rw [←pow_mul,mul_comm,pow_succ X 80])

theorem bounded {k p a B D : ℕ} (pr : 2≤p) (small : p≤32+4*(k+1))
    (poly : B≤16*(K k p a)^5) (little : 2^k*p^a≤(B+1)^D) : B≤cutoff D := by
  let n:=k+a+34
  let X:=8*n
  let j:=82*D
  have large : 16≤X:=by dsimp [X,n];omega
  have bnd : B≤X^81:=poly.trans (cost_bound small)
  have plus : B+1≤X^82:=by
    have pos : 0<X^81:=pow_pos (by omega) _
    have dbl:=Nat.mul_le_mul_left (X^81) (show 2≤X by omega)
    rw [show (82:ℕ)=81+1 by decide,pow_succ]
    omega
  have raw : 2^(k+a)≤X^j:=calc
    _ = 2^k*2^a := pow_add .. 
    _ ≤ 2^k*p^a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left pr _)
    _ ≤ (B+1)^D := little
    _ ≤ (X^82)^D := Nat.pow_le_pow_left plus _
    _ = X^j := (pow_mul ..).symm
  have nbound : n≤16*(j+1)^2+68+6*j:=by
    by_cases high : 16*(j+1)^2≤n
    · have abs:=OMA.ComplementarySize245212.absorb high
      have sq:=Nat.pow_le_pow_left raw 2
      have dbl : 2^(2*(k+a))≤2^(6*j)*n^(2*j):=by
        dsimp only [X] at sq
        have form : ((8*n)^j)^2=2^(6*j)*n^(2*j):=by
          rw [←pow_mul,mul_pow,show (8:ℕ)=2^3 by decide,←pow_mul]
          rw [show 3*(j*2)=6*j by ring,show j*2=2*j by ring]
        simpa only [form,←pow_mul,Nat.mul_comm (k+a) 2] using sq
      have join : 2^(2*(k+a))≤2^(6*j+n):=by
        rw [pow_add]
        exact dbl.trans (Nat.mul_le_mul_left _ abs)
      have ex:=(pow_le_pow_iff_right₀ (a:=(2:ℕ)) (by decide)).mp join
      dsimp only [n] at ex ⊢
      omega
    · omega
  exact bnd.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 nbound) 81)

end OMA.MiddlePoleFinite245212

end

section

/- Whole-integer absolute bound in the three-odd-prime case from the
sorted-range cover, exact mixed equation, and integral cofactor gap. -/
namespace OMA.MiddleClose245212
open Nat ArithmeticFunction
open OMA.Smooth245212 (W)
open scoped ArithmeticFunction.sigma

theorem no_escape {D k p q a b d : ℕ} (pp : p.Prime) (op : Odd p) (qg : 2≤q)
    (high : OMA.MiddlePoleFinite245212.cutoff D < b+1)
    (mixed : OMA.MiddleBridge245212.output D k p q a b d) : False := by
  obtain ⟨small,cofactor,formula,side⟩:=mixed
  have gt : (d+1)*W (2^k*p^a)<(q-1)*σ 1 (2^k*p^a):=by
    simpa only [mul_comm] using side
  have poly := OMA.MiddlePoleOriginal245212.original pp op qg (Nat.succ_pos b) (Nat.succ_pos d) gt formula
  exact high.not_ge (OMA.MiddlePoleFinite245212.bounded pp.two_le
    (small.trans (Nat.le_add_left _ _)) poly cofactor)

theorem finish
    (ranges : ∀ N : ℕ, ∃ K : ℕ, ∀ {k p q r a b d : ℕ}, p.Prime → q.Prime → r.Prime →
      3≤p → p<q → q<r → 0<a → 0<b → 0<d →
      OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ) →
      2^k*p^a*q^b*r^d≤K ∨ (256≤k ∧ 33≤p ∧ N≤b+1 ∧ 16*(a+1)<b+1 ∧ 16*(d+1)<b+1)) :
    ∃ K : ℕ, ∀ {k p q r a b d : ℕ}, p.Prime → q.Prime → r.Prime →
      3≤p → p<q → q<r → 0<a → 0<b → 0<d →
      OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ) →
      2^k*p^a*q^b*r^d≤K := by
  let x:=OMA.MiddleBridge245212.threshold
  let y:=OMA.MiddlePoleFinite245212.cutoff OMA.MiddleBridge245212.exponent
  obtain ⟨K,cover⟩:=ranges (x+y+1)
  refine ⟨K,?_⟩
  intro k p q r a b d pp qp rp p3 pq qr ap bp dp eqn
  obtain small|⟨k0,p33,L,left,right⟩:=cover pp qp rp p3 pq qr ap bp dp eqn
  · exact small
  · have xL : x≤b+1:=((Nat.le_add_right _ _).trans (Nat.le_succ _)).trans L
    have yL : y<b+1:=(Nat.lt_succ_of_le (Nat.le_add_left _ _)).trans_le L
    have mixed:=OMA.MiddleBridge245212.original pp qp rp p33 pq qr ap bp dp k0 xL left right eqn
    exact False.elim (no_escape pp (pp.odd_of_ne_two (by omega)) qp.two_le yL mixed)

end OMA.MiddleClose245212

end

section

/- Outside a computably bounded set, only a long middle-prime exponent
can occur, and each of the other two lengths is less than a sixteenth of it. -/
namespace OMA.MiddleEscapeRanges245212
open Nat Finset ArithmeticFunction OMA.Smooth245212 OMA.TwoTallFinite245212 OMA.TwoTallConsequences245212
open scoped ArithmeticFunction.sigma
open OMA.TwoTallConsequences245212 (from_order)

def cap (N : ℕ) := (∑ j∈range 256, OMA.RankThreeEffective245212.bound j) +
  OMA.LeastTallOriginal245212.bound + valueCap 20 + valueCap N + valueCap 16

theorem at_cap (N : ℕ) {k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p3 : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    2^k*p^a*q^b*r^d≤cap N ∨
    (256≤k ∧ 33≤p ∧ N≤b+1 ∧ 16*(a+1)<b+1 ∧ 16*(d+1)<b+1) := by
  classical
  have op:=pp.odd_of_ne_two (by omega)
  have oq:=qp.odd_of_ne_two (by omega)
  have hr:=rp.odd_of_ne_two (by omega)
  let P : Fin 3→ℕ:=![p,q,r]
  let E : Fin 3→ℕ:=![a,b,d]
  have hp (i) : (P i).Prime:=by fin_cases i <;> simp [P,pp,qp,rp]
  have odd (i) : Odd (P i):=by fin_cases i <;> simp [P,op,oq,hr]
  have inj : P.Injective:=by intro i j h;fin_cases i <;> fin_cases j <;> simp_all [P] <;> omega
  have pos (i) : 0<E i:=by fin_cases i <;> simp [E,ap,bp,dp]
  have repr : 2^k*total P E=2^k*p^a*q^b*r^d:=by simp [total,Fin.prod_univ_three,P,E,mul_assoc]
  have ev : OeisA245212.a (2^k*total P E)=(σ 1 (2^k*total P E):ℤ):=by rwa [repr]
  by_cases biga : max b d≤a
  · have bound:=OMA.LeastTallOriginal245212.original k P E hp odd inj pos
      (by intro i;fin_cases i <;> simp [P] <;> omega)
      (by intro i;fin_cases i <;> simp [E] <;> omega) ev
    rw [repr] at bound
    left; unfold cap; omega
  by_cases bigd : max a b≤d
  · have bound:=OMA.TwoTallConsequences245212.largest_at_largest pp qp rp p3 pq qr ap bp dp bigd eqn
    left; unfold cap; omega
  have ab : a≤b:=by omega
  have db : d≤b:=by omega
  by_cases short : b+1<N
  · have bound:=OMA.TwoTallConsequences245212.from_order (C:=N) pp qp rp op oq hr pq.ne (pq.trans qr).ne qr.ne ap bp dp
      (m:=1) (L:=b+1) (by omega) (by omega) (by omega) (by simpa using short.le) eqn
    left; unfold cap; omega
  by_cases tall : b+1≤16*(a+1)
  · have bound:=OMA.TwoTallConsequences245212.from_order (C:=16) pp qp rp op oq hr pq.ne (pq.trans qr).ne qr.ne ap bp dp
      (m:=a+1) (L:=b+1) (by omega) (by omega) (by omega) tall eqn
    left; unfold cap; omega
  by_cases tail : b+1≤16*(d+1)
  · have aux:=OMA.TwoTallConsequences245212.from_order (C:=16) (k:=k) (a:=b) (b:=d) (d:=a) qp rp pp oq hr op qr.ne pq.ne.symm
      (pq.trans qr).ne.symm bp dp ap (m:=d+1) (L:=b+1) (by omega) (by omega) (by omega) tail
      (by simpa only [mul_comm,mul_assoc,mul_left_comm] using eqn)
    have bound : 2^k*p^a*q^b*r^d≤valueCap 16:=by simpa only [mul_comm,mul_assoc,mul_left_comm] using aux
    left; unfold cap; omega
  have om : Odd (total P E) := Nat.coprime_two_left.mp
    (Coprime.prod_right (fun i _ => (Nat.coprime_two_left.mpr (odd i)).pow_right _))
  have dv i : P i∣total P E := (dvd_pow_self _ (pos i).ne').trans
    (dvd_prod_of_mem (fun j => P j^E j) (mem_univ i))
  have mem i : P i∈(total P E).primeFactors:=mem_primeFactors.mpr ⟨hp i,dv i,om.pos.ne'⟩
  by_cases low : k<256
  · have image : (total P E).primeFactors=univ.image P := by
      ext z
      constructor
      · intro hz
        have pr:=prime_of_mem_primeFactors hz
        obtain ⟨i,_,di⟩:=(pr.prime.dvd_finsetProd_iff _).mp (dvd_of_mem_primeFactors hz : z∣∏i,P i^E i)
        exact mem_image.mpr ⟨i,mem_univ _,((prime_dvd_prime_iff_eq pr (hp i)).mp (pr.dvd_of_dvd_pow di)).symm⟩
      · rintro hz
        obtain ⟨i,_,rfl⟩:=mem_image.mp hz
        exact mem i
    have rk : (total P E).primeFactors.card=3:=by rw [image,card_image_of_injective _ inj];simp
    have bound:=OMA.RankThreeEffective245212.original om rk ev
    rw [repr] at bound
    have sum:=single_le_sum (f:=OMA.RankThreeEffective245212.bound) (fun _ _=>Nat.zero_le _) (mem_range.mpr low)
    left; unfold cap; omega
  have lim:=OMA.DyadicLeast245212.exponent_lt_twice_prime om (mem 0) ev
  change k<2*p at lim
  right; omega

theorem ranges (N : ℕ) : ∃ K : ℕ, ∀ {k p q r a b d : ℕ}, p.Prime → q.Prime → r.Prime →
    3≤p → p<q → q<r → 0<a → 0<b → 0<d →
    OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ) →
    2^k*p^a*q^b*r^d≤K ∨ (256≤k ∧ 33≤p ∧ N≤b+1 ∧ 16*(a+1)<b+1 ∧ 16*(d+1)<b+1) :=
  ⟨cap N, fun {_ _ _ _ _ _ _} => at_cap N⟩
end OMA.MiddleEscapeRanges245212

end

section

/- An absolute computable whole-integer height for the three odd prime case,
also stated directly in terms of the support of an arbitrary positive integer. -/
namespace OMA.ThreeOddAbsolute245212
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open OMA.MiddleClose245212 (no_escape)

def cutoff := OMA.MiddleEscapeRanges245212.cap
  (OMA.MiddleBridge245212.threshold+OMA.MiddlePoleFinite245212.cutoff OMA.MiddleBridge245212.exponent+1)

theorem ordered {k p q r a b d : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (p3 : 3≤p) (pq : p<q) (qr : q<r) (ap : 0<a) (bp : 0<b) (dp : 0<d)
    (eqn : OeisA245212.a (2^k*p^a*q^b*r^d)=(σ 1 (2^k*p^a*q^b*r^d):ℤ)) :
    2^k*p^a*q^b*r^d≤cutoff := by
  let x:=OMA.MiddleBridge245212.threshold
  let y:=OMA.MiddlePoleFinite245212.cutoff OMA.MiddleBridge245212.exponent
  obtain low|⟨k0,p33,L,left,right⟩:= OMA.MiddleEscapeRanges245212.at_cap (x+y+1) pp qp rp p3 pq qr ap bp dp eqn
  · exact low
  · have xL : x≤b+1:=((Nat.le_add_right _ _).trans (Nat.le_succ _)).trans L
    have yL : y<b+1:=(Nat.lt_succ_of_le (Nat.le_add_left _ _)).trans_le L
    have mixed:=OMA.MiddleBridge245212.original pp qp rp p33 pq qr ap bp dp k0 xL left right eqn
    exact False.elim (OMA.MiddleClose245212.no_escape pp (pp.odd_of_ne_two (by omega)) qp.two_le yL mixed)

theorem odd_part {k m : ℕ} (odd : Odd m) (rank : m.primeFactors.card=3)
    (eqn : OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ)) : 2^k*m≤cutoff := by
  let P : Fin 3 ↪o ℕ := m.primeFactors.orderEmbOfFin rank
  let e (i : Fin 3):=m.factorization (P i)
  have mem (i : Fin 3) : P i∈m.primeFactors := m.primeFactors.orderEmbOfFin_mem rank i
  have pr (i) := prime_of_mem_primeFactors (mem i)
  have ep (i) : 0<e i := (pr i).factorization_pos_of_dvd odd.pos.ne' (dvd_of_mem_primeFactors (mem i))
  have oddp:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right (dvd_of_mem_primeFactors (mem 0)))
  have least : 3≤P 0 := by have := (pr 0).two_le;obtain ⟨j,hj⟩:=oddp;omega
  have prod:=Nat.prod_primeFactors_pow_factorization odd.pos.ne'
  have lift : Finset.univ.map P.toEmbedding=m.primeFactors := m.primeFactors.map_orderEmbOfFin_univ rank
  rw [←lift,prod_map,Fin.prod_univ_three] at prod
  change m=(P 0)^(e 0)*(P 1)^(e 1)*(P 2)^(e 2) at prod
  have repr : 2^k*m=2^k*(P 0)^(e 0)*(P 1)^(e 1)*(P 2)^(e 2) := by
    simpa only [mul_assoc] using congrArg (2^k*·) prod
  rw [repr] at eqn ⊢
  exact ordered (pr 0) (pr 1) (pr 2) least (P.strictMono (by decide : (0:Fin 3)<1))
    (P.strictMono (by decide : (1:Fin 3)<2)) (ep 0) (ep 1) (ep 2) eqn

theorem original {n : ℕ} (pos : 0<n) (rank : (n.primeFactors.erase 2).card=3)
    (eqn : OeisA245212.a n=(σ 1 n:ℤ)) : n≤cutoff := by
  let m:=ordCompl[2] n
  let k:=n.factorization 2
  have cm : Odd m:=Nat.coprime_two_left.mp (Nat.coprime_ordCompl prime_two pos.ne')
  have ss : m.primeFactors=n.primeFactors.erase 2 := by
    dsimp [m];rw [←Nat.support_factorization,Nat.factorization_ordCompl,Finsupp.support_erase,Nat.support_factorization]
  have id : 2^k*m=n:=Nat.ordProj_mul_ordCompl_eq_self n 2
  have h := odd_part (k:=k) cm (ss ▸ rank) (by rwa [id])
  rwa [id] at h

theorem finite : {n : ℕ | 0<n ∧ (n.primeFactors.erase 2).card=3 ∧ OeisA245212.a n=(σ 1 n:ℤ)}.Finite :=
  (Set.finite_Iic cutoff).subset (fun _ h=>original h.1 h.2.1 h.2.2)

end OMA.ThreeOddAbsolute245212

end






/-! Match the explicit finite search box to the kernel-checked modular definition. -/
private theorem rankThreeBudgetRec (A r : ℕ) :
    OMA.CofactorEulerSeparation245212.budget A r =
    Nat.rec 1 (fun i t=>max (2*t) ((2+2*A*2^i*t)^(i+1))) r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [OMA.CofactorEulerSeparation245212.budget, ih]

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H2_R3_H3_R1.H1 := by
  unfold OMA.R_OeisA245212_conjecture_R1_H2_R3_H3_R1.H1
  intro w step fixed dy core f v D C s j N K k m odd rank eqn
  have bound := OMA.ThreeOddAbsolute245212.odd_part odd rank eqn
  have stepEq : step=OMA.RankThreeEffective245212.stepBound := by
    funext h r
    simp only [step, w, OMA.RankThreeEffective245212.stepBound,
      OMA.CofactorEffectiveOriginal245212.primeHeight, OMA.CofactorEffectiveOriginal245212.height,
      OMA.CofactorEffectiveAtom245212.threshold, rankThreeBudgetRec, OMA.Smooth245212.W]
  have fixEq : fixed=OMA.RankThreeEffective245212.bound := by
    dsimp only [fixed];rw [stepEq];rfl
  have vEq : v=OMA.TwoTallFinite245212.valueCap := by
    dsimp only [v];rw [fixEq];rfl
  have goal : K=OMA.ThreeOddAbsolute245212.cutoff := by
    dsimp only [K];rw [vEq,fixEq];rfl
  exact goal.symm ▸ bound
