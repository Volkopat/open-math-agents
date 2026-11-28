import FormalConjectures.ErdosProblems.«189»
import Mathlib

/-!
# The prescribed-area parallelogram variant of Erdős 189

Use opposite pairs about a common centre. In shear coordinates the area between
the two diagonals, divided by two, is the difference of their parameters divided
by the product of their row labels. Avoidance therefore gives zero incidences
at shifts proportional to a product of two real numbers. A second-moment
argument rules this out for rows of positive mean density.
-/

open Filter Finset
open scoped Topology BigOperators

namespace E189
noncomputable section

def Bd {X : Type*} (f : X → ℝ) : Prop := ∃ C : ℝ, ∀ x, |f x| ≤ C

theorem bd_const {X : Type*} (a : ℝ) : Bd (fun _ : X => a) := ⟨|a|, fun _ => le_rfl⟩
theorem Bd.comp {X Y : Type*} {f : X → ℝ} (h : Bd f) (g : Y → X) : Bd (fun y => f (g y)) :=
  let ⟨C,hC⟩ := h; ⟨C, fun y => hC (g y)⟩
theorem Bd.add {X : Type*} {f g : X → ℝ} (h : Bd f) (k : Bd g) : Bd (fun x => f x + g x) := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := k
  exact ⟨a+b, fun x => (abs_add_le ..).trans (add_le_add (ha x) (hb x))⟩
theorem Bd.mul {X : Type*} {f g : X → ℝ} (h : Bd f) (k : Bd g) : Bd (fun x => f x * g x) := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := k
  exact ⟨a*b, fun x => by rw [abs_mul]; exact mul_le_mul (ha x) (hb x) (abs_nonneg _) ((abs_nonneg _).trans (ha x))⟩
theorem Bd.sub {X : Type*} {f g : X → ℝ} (h : Bd f) (k : Bd g) : Bd (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using h.add ((bd_const (-1)).mul k)
theorem bd_sum {X I : Type*} (s : Finset I) (f : I → X → ℝ) (h : ∀ i ∈ s, Bd (f i)) :
    Bd (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bd_const (X := X) 0
  | insert i s hi ih =>
    simpa [hi] using (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

structure Av (X : Type*) where
  eval : (X → ℝ) → ℝ
  const : ∀ a : ℝ, eval (fun _ => a) = a
  add : ∀ {f g}, Bd f → Bd g → eval (fun x => f x + g x) = eval f + eval g
  smul : ∀ (a : ℝ) {f}, Bd f → eval (fun x => a * f x) = a * eval f
  mono : ∀ {f g}, Bd f → Bd g → (∀ x, f x ≤ g x) → eval f ≤ eval g

instance {X : Type*} : CoeFun (Av X) (fun _ => (X → ℝ) → ℝ) := ⟨Av.eval⟩

theorem Av.bound {X : Type*} (m : Av X) {f : X → ℝ} {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    |m f| ≤ C := by
  have h : Bd f := ⟨_,hf⟩
  apply abs_le.mpr
  constructor
  · simpa [m.const] using m.mono (bd_const (-C)) h (fun x => (abs_le.mp (hf x)).1)
  · simpa [m.const] using m.mono h (bd_const C) (fun x => (abs_le.mp (hf x)).2)

theorem Av.sum {X I : Type*} (m : Av X) (s : Finset I) (f : I → X → ℝ) (hf : ∀ i ∈ s, Bd (f i)) :
    m (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [m.const]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [m.add (hf i (by simp)) (bd_sum s f (fun j hj => hf j (by simp [hj])))]
    rw [ih (fun j hj => hf j (by simp [hj]))]

def dirac {X : Type*} (x : X) : Av X where
  eval f := f x
  const _ := rfl
  add _ _ := rfl
  smul _ {_} _ := rfl
  mono _ _ h := h x

def Av.map {X Y : Type*} (m : Av X) (t : X → Y) : Av Y where
  eval f := m (fun x => f (t x))
  const := m.const
  add h k := m.add (h.comp t) (k.comp t)
  smul a {_} h := m.smul a (h.comp t)
  mono h k e := m.mono (h.comp t) (k.comp t) (fun x => e (t x))

def Av.bind {X Y : Type*} (m : Av X) (n : X → Av Y) : Av Y where
  eval f := m (fun x => n x f)
  const a := by simp only [Av.const, m.const]
  add {f g} hf hg := by
    simp only [(n _).add hf hg]
    exact m.add (let ⟨c,h⟩ := hf; ⟨c, fun x => (n x).bound h⟩)
      (let ⟨c,h⟩ := hg; ⟨c, fun x => (n x).bound h⟩)
  smul a {_} h := by
    simp only [(n _).smul a h]
    exact m.smul a (let ⟨c,hc⟩ := h; ⟨c, fun x => (n x).bound hc⟩)
  mono h k e := m.mono (let ⟨c,hc⟩ := h; ⟨c, fun x => (n x).bound hc⟩)
    (let ⟨c,hc⟩ := k; ⟨c, fun x => (n x).bound hc⟩) (fun x => (n x).mono h k e)

theorem ultraConv {X : Type*} (u : Ultrafilter X) {f : X → ℝ} (h : Bd f) :
    Tendsto f u (𝓝 (limUnder u f)) := by
  obtain ⟨C,hC⟩ := h
  apply tendsto_nhds_limUnder
  obtain ⟨x, _, hx⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds (u.map f)
    (by apply Filter.le_principal_iff.mpr; change ∀ᶠ x in (u : Filter X), f x ∈ Set.Icc (-C) C; exact Filter.Eventually.of_forall (fun x => abs_le.mp (hC x)))
  exact ⟨x,hx⟩

def ultraAv {X : Type*} (u : Ultrafilter X) : Av X where
  eval f := limUnder u f
  const _a := tendsto_const_nhds.limUnder_eq
  add hf hg := ((ultraConv u hf).add (ultraConv u hg)).limUnder_eq
  smul _a {_} hf := (tendsto_const_nhds.mul (ultraConv u hf)).limUnder_eq
  mono hf hg h := le_of_tendsto_of_tendsto' (ultraConv u hf) (ultraConv u hg) h

end
end E189

/- Translation and dilation invariant averages. -/
open Filter Finset
open scoped Topology BigOperators
namespace E189
noncomputable section

def initial (n : ℕ) : Av ℕ where
  eval f := (∑ j ∈ range (n+1), f j) / (n+1 : ℝ)
  const a := by simp; field_simp
  add _ _ := by simp [sum_add_distrib, add_div]
  smul a {_} _ := by rw [← Finset.mul_sum]; ring
  mono _ _ h := by apply div_le_div_of_nonneg_right _ (by positivity); exact sum_le_sum fun j _ => h j

def natAv : Av ℕ := (ultraAv (Ultrafilter.of atTop)).bind initial

theorem natAv_shift {f : ℕ → ℝ} (hf : Bd f) : natAv (fun j => f (j+1)) = natAv f := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  let a := fun n => initial n f
  let b := fun n => initial n (fun j => f (j+1))
  have ba : Bd a := let ⟨C,h⟩ := hf; ⟨C,fun n => (initial n).bound h⟩
  have bb : Bd b := let ⟨C,h⟩ := hf; ⟨C,fun n => (initial n).bound (fun j => h (j+1))⟩
  have e (n : ℕ) : b n - a n = (f (n+1) - f 0)/(n+1 : ℝ) := by
    change _ / _ - _ / _ = _
    rw [← sub_div]
    congr 1
    have h := Finset.sum_range_succ' f (n+1)
    rw [Finset.sum_range_succ] at h
    linarith
  obtain ⟨C,hC⟩ := hf
  have ht : Tendsto (fun n => b n - a n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : ℕ => (C+C)/(n+1 : ℝ))
    · apply Eventually.of_forall
      intro n
      rw [e, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (n+1 : ℝ))]
      gcongr
      exact (abs_sub _ _).trans (add_le_add (hC _) (hC _))
    · simpa [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat (C+C)).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_nhds_unique ((ultraConv u bb).sub (ultraConv u ba))
    (ht.mono_left (Ultrafilter.of_le atTop))
  exact sub_eq_zero.mp he

def Inv {G : Type*} [CommGroup G] (m : Av G) (a : G) : Prop :=
  ∀ f : G → ℝ, Bd f → m (fun x => f (a*x)) = m f

private def sweep {G : Type*} [CommGroup G] (m : Av G) (a : G) : Av G :=
  natAv.bind fun j => m.map fun x => a^j*x

private theorem sweep_self {G : Type*} [CommGroup G] (m : Av G) (a : G) : Inv (sweep m a) a := by
  intro f hf
  let g := fun j : ℕ => m (fun x => f (a^j*x))
  have hg : Bd g := let ⟨C,h⟩ := hf; ⟨C,fun j => m.bound (fun x => h _)⟩
  change natAv (fun j : ℕ => m (fun x => f (a*(a^j*x)))) = natAv g
  rw [← natAv_shift hg]
  apply congrArg natAv.eval
  funext j
  apply congrArg m.eval
  funext x
  simp only [pow_succ]; ac_rfl

private theorem sweep_keep {G : Type*} [CommGroup G] {m : Av G} {b : G} (hb : Inv m b) (a : G) :
    Inv (sweep m a) b := by
  intro f hf
  change natAv (fun j : ℕ => m (fun x => f (b*(a^j*x)))) = natAv (fun j : ℕ => m (fun x => f (a^j*x)))
  apply congrArg natAv.eval
  funext j
  simpa only [mul_left_comm b] using hb (fun x => f (a^j*x)) (hf.comp _)

private theorem finite_inv {G : Type*} [CommGroup G] (s : Finset G) :
    ∃ m : Av G, ∀ g ∈ s, Inv m g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨dirac 1, by simp⟩
  | insert a s _ ih =>
    obtain ⟨m,hm⟩ := ih
    refine ⟨sweep m a,fun g hg => ?_⟩
    rcases Finset.mem_insert.mp hg with rfl|hg
    · exact sweep_self _ _
    · exact sweep_keep (hm g hg) a

theorem comm_mean (G : Type*) [CommGroup G] : ∃ m : Av G, ∀ g, Inv m g := by
  classical
  choose family hf using (finite_inv (G := G))
  let u : Ultrafilter (Finset G) := Ultrafilter.of atTop
  refine ⟨(ultraAv u).bind family, fun g f h => ?_⟩
  apply congrArg Filter.lim
  apply Filter.map_congr
  apply (Ultrafilter.of_le atTop)
  filter_upwards [eventually_ge_atTop ({g} : Finset G)] with s hs
  exact hf s g (hs (by simp)) f h

structure AffAv extends Av ℝ where
  shift : ∀ (a : ℝ) {f}, Bd f → eval (fun x => f (x+a)) = eval f
  dil : ∀ {a : ℝ}, a ≠ 0 → ∀ {f}, Bd f → eval (fun x => f (a*x)) = eval f

instance : CoeFun AffAv (fun _ => (ℝ → ℝ) → ℝ) := ⟨fun m => m.eval⟩

theorem aff_mean : Nonempty AffAv := by
  obtain ⟨m,hm⟩ := comm_mean (Multiplicative ℝ)
  obtain ⟨n,hn⟩ := comm_mean ℝˣ
  let p := n.bind fun (a : ℝˣ) => m.map fun x => (a:ℝ) * Multiplicative.toAdd x
  refine ⟨{ toAv := p, shift := ?_, dil := ?_ }⟩
  · intro b f h
    change n (fun a : ℝˣ => m (fun x => f (↑a * Multiplicative.toAdd x + b))) =
      n (fun a : ℝˣ => m (fun x => f (↑a * Multiplicative.toAdd x)))
    apply congrArg n.eval
    funext a
    rw [← hm (Multiplicative.ofAdd (b/(a:ℝ))) (fun x => f ((a:ℝ)*Multiplicative.toAdd x)) (h.comp _)]
    apply congrArg m.eval
    funext x
    change f _ = f ((a:ℝ) * (b/(a:ℝ) + Multiplicative.toAdd x))
    congr 1
    field_simp; ring
  · intro b hb f h
    let v : ℝˣ := Units.mk0 b hb
    let g := fun a : ℝˣ => m (fun x => f ((a:ℝ)*Multiplicative.toAdd x))
    have hg : Bd g := let ⟨C,hC⟩ := h; ⟨C, fun a => m.bound (fun x => hC _)⟩
    change n (fun a : ℝˣ => m (fun x => f (b*(↑a*Multiplicative.toAdd x)))) = n g
    rw [← hn v g hg]
    apply congrArg n.eval
    funext a
    apply congrArg m.eval
    funext x
    change f (b*(_*_)) = f ((b*_)*_)
    rw [mul_assoc]

end
end E189

/- Scalar second-moment inequalities for positive averages. -/
open Finset
open scoped BigOperators
namespace E189
noncomputable section

theorem Av.nonneg {X : Type*} (m : Av X) {f : X → ℝ} (h : Bd f) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ m f := (m.const 0) ▸ m.mono (bd_const 0) h hf

theorem Av.sub {X : Type*} (m : Av X) {f g : X → ℝ} (hf : Bd f) (hg : Bd g) :
    m (fun x => f x - g x) = m f - m g := by
  have hh := m.add hf ((bd_const (-1)).mul hg)
  rw [m.smul _ hg] at hh
  simpa [sub_eq_add_neg] using hh

theorem Av.jensen {X : Type*} (m : Av X) {f : X → ℝ} (h : Bd f) :
    m f * m f ≤ m (fun x => f x * f x) := by
  let c := m f
  have hc : Bd (fun x => f x - c) := h.sub (bd_const c)
  have H := m.nonneg (hc.mul hc) (fun x => mul_self_nonneg _)
  have eq : (fun x => (f x-c)*(f x-c)) = fun x => (f x*f x - (2*c)*f x) + c*c := by
    funext; ring
  rw [eq, m.add ((h.mul h).sub ((bd_const _).mul h)) (bd_const _),
    m.sub (h.mul h) ((bd_const _).mul h), m.smul _ h, m.const] at H
  dsimp [c] at H
  linarith

theorem bound01 {X : Type*} {f : X → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Bd f :=
  ⟨1,fun x => by rw [abs_of_nonneg (hf x).1]; exact (hf x).2⟩

def iid {X : Type*} (m : Av X) : (n : ℕ) → Av (Fin n → X)
  | 0 => dirac Fin.elim0
  | n+1 => m.bind fun x => (iid m n).map fun a => Fin.cons (α := fun _ => X) x a

theorem iid_one {X : Type*} (m : Av X) {n : ℕ} (i : Fin n) (f : X → ℝ) :
    iid m n (fun a => f (a i)) = m f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change m (fun x => iid m n (fun a => f (Fin.cons (α := fun _ => X) x a 0))) = m f
      simp only [Fin.cons_zero, Av.const]
    · change m (fun x => iid m n (fun a => f (Fin.cons (α := fun _ => X) x a j.succ))) = m f
      simp only [Fin.cons_succ, ih j, Av.const]

theorem iid_pair {X : Type*} (m : Av X) {n : ℕ} (i j : Fin n) (ne : i ≠ j)
    (K : X → X → ℝ) (sym : ∀ a b, K a b = K b a) :
    iid m n (fun a => K (a i) (a j)) = m (fun a => m (K a)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert ne
    refine Fin.cases ?_ (fun u => ?_) i <;> refine Fin.cases ?_ (fun v => ?_) j
    · simp
    · intro _
      change m (fun x => iid m n (fun a => K (Fin.cons (α := fun _ => X) x a 0) (Fin.cons (α := fun _ => X) x a v.succ))) = _
      simp only [Fin.cons_zero, Fin.cons_succ, iid_one]
    · intro _
      change m (fun x => iid m n (fun a => K (Fin.cons (α := fun _ => X) x a u.succ) (Fin.cons (α := fun _ => X) x a 0))) = _
      simp only [Fin.cons_zero, Fin.cons_succ]
      apply congrArg m.eval
      funext x
      rw [iid_one m u (fun y => K y x)]
      apply congrArg m.eval
      funext y
      exact sym _ _
    · intro uv
      change m (fun x => iid m n (fun a => K (Fin.cons (α := fun _ => X) x a u.succ) (Fin.cons (α := fun _ => X) x a v.succ))) = _
      simp only [Fin.cons_succ, ih u v (fun h => uv (congrArg Fin.succ h)), Av.const]

theorem no_linear_growth {b C : ℝ} (h : ∀ n : ℕ, (n:ℝ)*b ≤ C) : b ≤ 0 := by
  by_contra! hb
  obtain ⟨n,hn⟩ := exists_nat_gt (C/b)
  exact (not_lt_of_ge (h n)) ((div_lt_iff₀ hb).mp hn)

/-- Integrating a bounded positive semidefinite kernel twice is nonnegative.
Sample a finite tuple independently and discard its diagonal after normalization. -/
theorem mean_gram_nonneg {X : Type*} (m : Av X) (K : X → X → ℝ)
    (sym : ∀ a b, K a b = K b a) {C : ℝ} (hb : ∀ a b, |K a b| ≤ C)
    (pos : ∀ (n : ℕ) (v : Fin n → X), 0 ≤ ∑ i, ∑ j, K (v i) (v j)) :
    0 ≤ m (fun a => m (K a)) := by
  classical
  let D := m (fun a => K a a)
  let V := m (fun a => m (K a))
  have hn (n : ℕ) : 0 ≤ (n:ℝ)*D+(n:ℝ)*((n:ℝ)-1)*V := by
    let z := iid m n
    have H := z.nonneg (bd_sum univ _ (fun i _ => bd_sum univ _ (fun j _ =>
      (show Bd (fun a : Fin n → X => K (a i) (a j)) from ⟨C,fun _ => hb _ _⟩)))) (pos n)
    rw [z.sum univ _ (fun i _ => bd_sum univ _ (fun j _ => ⟨C,fun _ => hb _ _⟩))] at H
    simp_rw [z.sum univ _ (fun j _ => ⟨C,fun _ => hb _ _⟩)] at H
    have term (i j : Fin n) : z (fun a => K (a i) (a j)) = (if i=j then D-V else 0)+V := by
      by_cases e : i=j
      · subst j; simpa [D,z] using iid_one m i (fun a => K a a)
      · simp [e,z,iid_pair m i j e K sym,V]
    simp_rw [term, sum_add_distrib] at H
    simp [Finset.sum_ite_eq] at H
    linarith
  have hg (n : ℕ) : (n:ℝ)*(-V) ≤ D := by
    have h := hn (n+1)
    push_cast at h
    have eq : ((n:ℝ)+1)*D+((n:ℝ)+1)*((n:ℝ)+1-1)*V = ((n:ℝ)+1)*(D+(n:ℝ)*V) := by ring
    rw [eq] at h
    have h' := nonneg_of_mul_nonneg_right h (show (0:ℝ)<n+1 by positivity)
    linarith
  linarith [no_linear_growth hg]

/-- Apply positivity of the centred Gram kernel to recover the squared mean. -/
theorem gram_mean_lower {X Y : Type*} (m : Av X) (z : Av Y)
    (f : X → Y → ℝ) (hf : ∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) :
    (m (fun a => z (f a)))^2 ≤ m (fun a => m (fun b => z (fun y => f a y * f b y))) := by
  let d := m (fun a => z (f a))
  let g := fun a y => f a y - d
  have h1 (a) := bound01 (hf a)
  have hg (a) : Bd (g a) := (h1 a).sub (bd_const d)
  have hg' (a y) : |g a y| ≤ 1+|d| := (abs_sub _ _).trans
    (add_le_add (show |f a y| ≤ 1 by rw [abs_of_nonneg (hf a y).1]; exact (hf a y).2) (le_refl |d|))
  let K := fun a b => z (fun y => g a y * g b y)
  have H := mean_gram_nonneg m K (fun a b => by simp only [K,mul_comm])
    (C := (1+|d|)*(1+|d|)) (fun a b => z.bound (fun y => by
      rw [abs_mul]; exact mul_le_mul (hg' _ _) (hg' _ _) (abs_nonneg _) (by positivity))) (by
      intro n v
      have B := bd_sum univ (fun i => g (v i)) (fun i _ => hg _)
      have t := z.nonneg (B.mul B) (fun y => mul_self_nonneg _)
      simp_rw [Finset.sum_mul, Finset.mul_sum] at t
      rw [z.sum univ _ (fun i _ => bd_sum univ _ (fun j _ => (hg _).mul (hg _)))] at t
      simpa only [z.sum univ _ (fun j _ => (hg _).mul (hg _))] using t)
  have dz : Bd (fun a => z (f a)) := ⟨1,fun a => z.bound (fun y => by
    rw [abs_of_nonneg (hf a y).1]; exact (hf a y).2)⟩
  have kc (a b) : |z (fun y => f a y*f b y)| ≤ 1 := z.bound (fun y => by
    rw [abs_of_nonneg (mul_nonneg (hf _ _).1 (hf _ _).1)]
    nlinarith [(hf a y).1,(hf b y).2,mul_nonneg (hf a y).1 (sub_nonneg.mpr (hf b y).2),(hf a y).2])
  have kg (a b) : K a b = z (fun y => f a y * f b y) - d*z (f a) - d*z (f b) + d*d := by
    change z (fun y => (f a y-d)*(f b y-d)) = _
    simp_rw [show ∀ x y : ℝ, (x-d)*(y-d)=x*y-d*x-d*y+d*d by intros;ring]
    rw [z.add ((((h1 a).mul (h1 b)).sub ((bd_const d).mul (h1 a))).sub ((bd_const d).mul (h1 b))) (bd_const _),
      z.sub (((h1 a).mul (h1 b)).sub ((bd_const d).mul (h1 a))) ((bd_const d).mul (h1 b)),
      z.sub ((h1 a).mul (h1 b)) ((bd_const d).mul (h1 a)), z.smul _ (h1 a), z.smul _ (h1 b), z.const]
  have krow (a) : m (K a) = m (fun b => z (fun y => f a y*f b y)) - d*z (f a) := by
    change m (fun b => K a b) = _
    simp_rw [kg]
    have hb : Bd (fun b => z (fun y => f a y*f b y)) := ⟨1,kc a⟩
    rw [m.add ((hb.sub (bd_const _)).sub ((bd_const d).mul dz)) (bd_const _),
      m.sub (hb.sub (bd_const _)) ((bd_const d).mul dz),m.sub hb (bd_const _),m.smul _ dz,m.const,m.const]
    dsimp [d];ring
  simp_rw [krow] at H
  have hrow : Bd (fun a => m (fun b => z (fun y => f a y*f b y))) :=
    ⟨1,fun a => m.bound (kc a)⟩
  rw [m.sub hrow ((bd_const d).mul dz),m.smul _ dz] at H
  dsimp [d] at H
  linarith

end
end E189

/- Finite exceptional sets and an orthogonality bound. -/
open Finset
open scoped BigOperators
namespace E189
noncomputable section

def atom (a x : ℝ) : ℝ := if x=a then 1 else 0
theorem batom (a : ℝ) : Bd (atom a) := ⟨1,fun x => by unfold atom; split <;> norm_num⟩

theorem atom_zero (m : AffAv) (a : ℝ) : m (atom a) = 0 := by
  have eq (b : ℝ) : m (atom b) = m (atom a) := by
    rw [← m.shift (a-b) (batom a)]
    apply congrArg m.eval
    funext x
    simp only [atom, show x+(a-b)=a ↔ x=b by constructor <;> intro h <;> linarith]
  have h (n : ℕ) : (n:ℝ)*m (atom a) ≤ 1 := by
    let f := fun (i : Fin n) => atom (i:ℕ)
    have B := bd_sum univ f (fun i _ => batom _)
    have H := m.toAv.mono B (bd_const 1) (fun x => show (∑ i, f i x) ≤ 1 from by
      by_cases hx : ∃ i : Fin n, x=(i.val:ℝ)
      · obtain ⟨i,rfl⟩ := hx
        have equiv (j : Fin n) : ((i.val:ℝ)=(j.val:ℝ)) ↔ i=j := by
          constructor
          · intro he; apply Fin.ext; exact_mod_cast he
          · rintro rfl; rfl
        simp only [f,atom,equiv]; simp
      · simp [f,atom,not_exists.mp hx])
    rw [m.toAv.const,m.toAv.sum _ _ (fun i _ => batom _)] at H
    simpa [f,eq] using H
  exact le_antisymm (no_linear_growth h) (m.toAv.nonneg (batom _) (fun x => by unfold atom; split <;> norm_num))

theorem AffAv.largeRows (m : AffAv) (f : ℝ → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : 0 < m f) : ∀ s : Finset ℝ, ∃ r ∉ s, m f / 2 < f r := by
  classical
  intro s
  by_contra! hh
  let spike := fun x : ℝ => ∑ a ∈ s, atom a x
  have hs : Bd spike := bd_sum s atom (fun i _ => batom i)
  have z : m spike = 0 := by
    rw [m.toAv.sum s atom (fun i _ => batom i)]
    simp only [show ∀ a, m.toAv (atom a) = 0 from atom_zero m, sum_const_zero]
  have H := m.toAv.mono (bound01 hf) ((bd_const (m f/2)).add hs) (fun x => by
    by_cases hx : x ∈ s
    · have hxe : spike x = 1 := by simp [spike, atom, hx]
      linarith [(hf x).2]
    · have hxe : spike x = 0 := by simp [spike,atom,hx]
      linarith [hh x hx])
  rw [m.toAv.add (bd_const _) hs,m.toAv.const,z] at H
  linarith

theorem AffAv.except_zero (m : AffAv) {f g : ℝ → ℝ} (_bf : Bd f) (bg : Bd g)
    (h : ∀ x, x ≠ 0 → f x = g x) : m f = m g := by
  let c := f 0 - g 0
  have e : f = fun x => g x + c*atom 0 x := by
    funext x
    by_cases hx : x=0
    · subst x; simp [c,atom]
    · simp [atom,hx,h x hx]
  rw [e,m.toAv.add bg ((bd_const c).mul (batom 0)),m.toAv.smul c (batom _),atom_zero]
  ring

theorem abs_orth_bound {X : Type*} (z : Av X) {n : ℕ} (w : Fin n → X → ℝ) (v : X → ℝ)
    (hw : ∀ i x, |w i x| ≤ 1) (hv : ∀ x, |v x| ≤ 1)
    (ho : ∀ i j, i≠j → z (fun x => w i x*w j x)=0)
    {d : ℝ} (hd : 0 < d) (hn : 0 < n) (hm : ∀ i, z (fun x => w i x*v x) ≤ -d) :
    (n:ℝ)*(d*d) ≤ 1 := by
  classical
  have bw (i) : Bd (w i) := ⟨1,hw i⟩
  have bv : Bd v := ⟨1,hv⟩
  let S := fun x => ∑ i, w i x
  have bS : Bd S := bd_sum univ w (fun i _ => bw i)
  have first : z (fun x => S x*v x) ≤ -(n:ℝ)*d := by
    simp only [S,Finset.sum_mul,z.sum univ _ (fun i _ => (bw i).mul bv)]
    simpa using Finset.sum_le_sum (s := univ) (fun i _ => hm i)
  have second : z (fun x => S x*S x) ≤ (n:ℝ) := by
    simp only [S,Finset.sum_mul,Finset.mul_sum]
    rw [z.sum univ _ (fun i _ => bd_sum univ _ (fun j _ => (bw j).mul (bw i)))]
    simp_rw [z.sum univ _ (fun j _ => (bw j).mul (bw _))]
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (if i=j then (1:ℝ) else 0) := by
        gcongr with i _ j _
        split_ifs with e
        · subst j
          rw [← z.const 1]
          apply z.mono ((bw i).mul (bw i)) (bd_const _)
          intro x
          nlinarith [(abs_le.mp (hw i x)).1,(abs_le.mp (hw i x)).2,
            mul_nonneg (sub_nonneg.mpr (abs_le.mp (hw i x)).2) (show 0 ≤ 1+w i x by linarith [(abs_le.mp (hw i x)).1])]
        · rw [ho j i (Ne.symm e)]
      _ = _ := by simp
  have jens := z.jensen (bS.mul bv)
  have top := z.mono ((bS.mul bv).mul (bS.mul bv)) (bS.mul bS) (fun x => by
    have xv := abs_le.mp (hv x)
    have h : v x*v x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr xv.2) (show 0 ≤ 1+v x by linarith [xv.1])]
    nlinarith [mul_nonneg (mul_self_nonneg (S x)) (sub_nonneg.mpr h)])
  have nn : (0:ℝ)<n := by exact_mod_cast hn
  have u := mul_self_le_mul_self (show 0 ≤ (n:ℝ)*d by positivity)
    (show (n:ℝ)*d ≤ -z (fun x => S x*v x) by linarith)
  have hh : (n:ℝ)*(n*(d*d)) ≤ n*1 := by nlinarith
  exact (mul_le_mul_iff_right₀ nn).mp hh

end
end E189

/- Incidence mixing for the two diagonal vectors of a parallelogram. -/
open Finset
open scoped BigOperators
namespace E189
noncomputable section

def Av.prod {X Y : Type*} (m : Av X) (n : Av Y) : Av (X × Y) :=
  m.bind fun x => n.map fun y => (x,y)

theorem AffAv.affine (m : AffAv) {a : ℝ} (ha : a ≠ 0) (b : ℝ) {f : ℝ → ℝ} (h : Bd f) :
    m (fun x => f (a*x+b)) = m f := (m.dil ha (h.comp (fun x => x+b))).trans (m.shift b h)

theorem unit_av {Y : Type*} (z : Av Y) {f : Y → ℝ} (h : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    0 ≤ z f ∧ z f ≤ 1 := ⟨z.nonneg (bound01 h) (fun y => (h y).1),
    (z.mono (bound01 h) (bd_const 1) (fun y => (h y).2)).trans_eq (z.const 1)⟩
theorem unit_mul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a*b ∧ a*b ≤ 1 := ⟨mul_nonneg ha.1 hb.1, by simpa using mul_le_mul ha.2 hb.2 hb.1 zero_le_one⟩

structure Shear (Y : Type*) extends Av Y where
  U : ℝ → Y → Y
  addU : ∀ a b y, U a (U b y) = U (a+b) y
  zeroU : ∀ y, U 0 y = y
  invU : ∀ a {f : Y → ℝ}, Bd f → eval (fun y => f (U a y)) = eval f

section
variable {Y : Type*} (z : Shear Y) (m : AffAv) (f : ℝ → Y → ℝ)
/-- Two rows with a relative shear displacement. -/
def corr (r s h : ℝ) : ℝ := z.eval (fun y => f r y * f s (z.U h y))
def smooth (r s : ℝ) : ℝ := m (corr z f r s)

variable (h : ∀ r y, 0 ≤ f r y ∧ f r y ≤ 1)

include h in
theorem ucorr (r s t : ℝ) : 0 ≤ corr z f r s t ∧ corr z f r s t ≤ 1 :=
  unit_av _ (fun _ => unit_mul (h _ _) (h _ _))

include h in
theorem usmooth (r s : ℝ) : 0 ≤ smooth z m f r s ∧ smooth z m f r s ≤ 1 :=
  unit_av m.toAv (ucorr z f h r s)

include h in
theorem shifted (r s a b : ℝ) :
    z.eval (fun y => f r (z.U a y)*f s (z.U b y)) = corr z f r s (b-a) := by
  unfold corr
  rw [← z.invU a ((bound01 (h r)).mul ((bound01 (h s)).comp _))]
  simp [z.addU]

include h in
theorem density_to_smooth :
    (m (fun r => z.eval (f r)))^2 ≤ m (fun r => m (smooth z m f r)) := by
  let J := m.toAv.prod m.toAv
  let e := fun (p : ℝ × ℝ) y => f p.1 (z.U p.2 y)
  have H := gram_mean_lower J z.toAv e (fun _ _ => h _ _)
  change (m (fun r => m (fun a => z.eval (fun y => f r (z.U a y)))))^2 ≤
    m (fun r => m (fun a => m (fun s => m (fun b => z.eval (fun y =>
      f r (z.U a y) * f s (z.U b y)))))) at H
  simp only [z.invU _ (bound01 (h _)),m.toAv.const,shifted z f h] at H
  have bshift (r s a) : m (fun b => corr z f r s (b-a)) = smooth z m f r s := by
    simpa only [smooth,sub_eq_add_neg] using m.shift (-a) (bound01 (ucorr z f h r s))
  simpa only [bshift,m.toAv.const] using H

def universeAv := m.toAv.prod (m.toAv.prod z.toAv)
def Xrow (c r : ℝ) (x : ℝ × ℝ × Y) := f r (z.U (c*r*x.1) x.2.2)
def Yrow (c r : ℝ) (x : ℝ × ℝ × Y) := f r (z.U (c*r*x.2.1) x.2.2)
def Wrow (c r : ℝ) (x : ℝ × ℝ × Y) := Xrow z f c r x - Yrow z f c r x
def testrow (x : ℝ × ℝ × Y) := f x.1 x.2.2

include h in
/-- Compare the shear at the tested row parameter against an independent shear.
For two different row labels all four cross-correlations have the same mean. -/
theorem row_orth {c r s : ℝ} (hc : c≠0) (hr : r≠0) (hs : s≠0) (hrs : r≠s) :
    universeAv z m (fun x => Wrow z f c r x * Wrow z f c s x) = 0 := by
  let P := universeAv z m
  let A := Xrow z f c
  let B := Yrow z f c
  let q := corr z f r s
  let C := smooth z m f r s
  have bq : Bd q := bound01 (ucorr z f h _ _)
  have br (i) : Bd (A i) := bound01 (fun _ => h _ _)
  have bs (i) : Bd (B i) := bound01 (fun _ => h _ _)
  have common : m (fun t => q (c*s*t-c*r*t)) = C := by
    change _ = m q
    convert m.affine (mul_ne_zero hc (sub_ne_zero.mpr (Ne.symm hrs))) 0 bq using 1
    apply congrArg m.eval; funext t; congr 1; ring
  have xx : P (fun x => A r x*A s x) = C := by
    change m (fun t => m (fun _ => z.eval (fun y => f r (z.U (c*r*t) y)*f s (z.U (c*s*t) y)))) = _
    simpa only [m.toAv.const,shifted z f h] using common
  have yy : P (fun x => B r x*B s x) = C := by
    change m (fun _ => m (fun t => z.eval (fun y => f r (z.U (c*r*t) y)*f s (z.U (c*s*t) y)))) = _
    simp only [m.toAv.const,shifted z f h]
    exact common
  have xy : P (fun x => A r x*B s x) = C := by
    change m (fun t => m (fun b => z.eval (fun y => f r (z.U (c*r*t) y)*f s (z.U (c*s*b) y)))) = _
    simp only [shifted z f h,sub_eq_add_neg]
    change m (fun t => m (fun b => q (c*s*b + -(c*r*t)))) = m q
    have inner (t : ℝ) := m.affine (mul_ne_zero hc hs) (-(c*r*t)) bq
    simp only [inner,m.toAv.const]
  have yx : P (fun x => B r x*A s x) = C := by
    change m (fun t => m (fun b => z.eval (fun y => f r (z.U (c*r*b) y)*f s (z.U (c*s*t) y)))) = _
    simp only [shifted z f h]
    have e (t b : ℝ) : c*s*t-c*r*b = (-(c*r))*b+c*s*t := by ring
    simp only [e]
    change m (fun t => m (fun b => q (-(c*r)*b+c*s*t))) = m q
    have inner (t : ℝ) := m.affine (neg_ne_zero.mpr (mul_ne_zero hc hr)) (c*s*t) bq
    simp only [inner,m.toAv.const]
  change P (fun x => (A r x - B r x)*(A s x-B s x))=0
  simp_rw [show ∀ a b c d : ℝ, (a-b)*(c-d) = (a*c-a*d) - b*c + b*d by intros;ring]
  rw [P.add ((((br r).mul (br s)).sub ((br r).mul (bs s))).sub ((bs r).mul (br s))) ((bs r).mul (bs s)),
    P.sub (((br r).mul (br s)).sub ((br r).mul (bs s))) ((bs r).mul (br s)),
    P.sub ((br r).mul (br s)) ((br r).mul (bs s)),xx,xy,yx,yy]
  ring

include h in
theorem row_test {c r : ℝ} (hc : c≠0) (hr : r≠0)
    (avoid : ∀ r s y, f r (z.U (c*r*s) y)*f s y=0) :
    universeAv z m (fun x => Wrow z f c r x * testrow f x) = -m (smooth z m f r) := by
  let P := universeAv z m
  let A := Xrow z f c r
  let B := Yrow z f c r
  let v := testrow f
  have ba : Bd A := bound01 (fun _ => h _ _)
  have bb : Bd B := bound01 (fun _ => h _ _)
  have bv : Bd v := bound01 (fun _ => h _ _)
  have xx : P (fun x => A x*v x) = 0 := by
    change m (fun t => m (fun _ => z.eval (fun y => f r (z.U (c*r*t) y)*f t y))) = 0
    simp only [avoid,z.toAv.const,m.toAv.const]
  have yy : P (fun x => B x*v x) = m (smooth z m f r) := by
    change m (fun t => m (fun b => z.eval (fun y => f r (z.U (c*r*b) y)*f t y))) = _
    apply congrArg m.eval;funext t
    have eq (b) := shifted z f h r t (c*r*b) 0
    simp only [z.zeroU,zero_sub,← neg_mul] at eq
    simp_rw [eq]
    simpa [smooth] using m.affine (neg_ne_zero.mpr (mul_ne_zero hc hr)) 0 (bound01 (ucorr z f h r t))
  change P (fun x => (A x - B x)*v x) = _
  simp_rw [sub_mul]
  rw [P.sub (ba.mul bv) (bb.mul bv),xx,yy,zero_sub]

include h in
/-- If a family of rows admits no incidences at any bilinear shift, its total density vanishes. -/
theorem incidence {c : ℝ} (hc : c≠0)
    (avoid : ∀ r s y, f r (z.U (c*r*s) y)*f s y=0) :
    m (fun r => z.eval (f r)) ≤ 0 := by
  classical
  by_contra! hp
  let row := fun r => m (smooth z m f r)
  have row01 (r) : 0 ≤ row r ∧ row r ≤ 1 := unit_av _ (usmooth z m f h r)
  have hrow : 0 < m row := lt_of_lt_of_le (sq_pos_of_pos hp) (density_to_smooth z m f h)
  let d := m row/2
  have hd : 0 < d := by dsimp [d]; positivity
  let good : Set ℝ := {r | r≠0 ∧ d < row r}
  have hi : good.Infinite := by
    intro hfin
    obtain ⟨r,hr,hr'⟩ := m.largeRows row row01 hrow (insert 0 hfin.toFinset)
    have hh : r≠0 ∧ r∉hfin.toFinset := by simpa using hr
    exact hh.2 (hfin.mem_toFinset.mpr ⟨hh.1,hr'⟩)
  let ids := Set.Infinite.natEmbedding good hi
  obtain ⟨n,hn⟩ := exists_nat_gt (1/(d*d))
  have hh := (div_lt_iff₀ (mul_pos hd hd)).mp hn
  have hn0 : 0 < n := by
    by_contra! hn'
    have hz : n=0 := Nat.le_zero.mp hn'
    rw [hz] at hh
    norm_num at hh
  let r := fun (i : Fin n) => ((ids i.val).val)
  have H := abs_orth_bound (universeAv z m) (fun i => Wrow z f c (r i)) (testrow f)
    (fun i x => by
      unfold Wrow Xrow Yrow
      exact abs_le.mpr ⟨by linarith [(h (r i) (z.U (c*r i*x.1) x.2.2)).1,(h (r i) (z.U (c*r i*x.2.1) x.2.2)).2],
        by linarith [(h (r i) (z.U (c*r i*x.1) x.2.2)).2,(h (r i) (z.U (c*r i*x.2.1) x.2.2)).1]⟩)
    (fun x => by unfold testrow; rw [abs_of_nonneg (h x.1 x.2.2).1]; exact (h _ _).2)
    (fun i j ne => row_orth z m f h hc (ids i).property.1 (ids j).property.1
      (fun e => ne (Fin.ext (ids.injective (Subtype.ext e)))))
    hd hn0 (fun i => (row_test z m f h hc (ids i).property.1 avoid).le.trans
      (neg_le_neg (ids i).property.2.le))
  linarith

end
end
end E189

/- The signed area, orientation and opposite lines required by the catalogue. -/
open Affine EuclideanGeometry
open scoped Real
namespace E189
noncomputable section
theorem area_coordinates (a b c : ℝ²) :
    dist a b * dist b c * (∡ a b c).sin =
      (a 0 - b 0) * (c 1 - b 1) - (a 1 - b 1) * (c 0 - b 0) := by
  let o : Orientation ℝ ℝ² (Fin 2) := Module.Oriented.positiveOrientation
  let u := a - b
  let v := c - b
  rw [dist_comm b c, dist_eq_norm, dist_eq_norm]
  change ‖u‖ * ‖v‖ * (o.oangle u v).sin = _
  rw [← o.norm_kahler, Orientation.oangle, Real.Angle.sin_coe, Complex.norm_mul_sin_arg]
  simp only [Orientation.kahler_apply_apply, Complex.add_im, Complex.ofReal_im,
    Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, zero_add, add_zero]
  rw [o.areaForm_to_volumeForm, o.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
    u, v, mul_comm]

def pt (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x, y]

private lemma corner_sign {a b c : ℝ²}
    (h : 0 < dist a b * dist b c * (∡ a b c).sin) : (∡ a b c).sign = 1 := by
  rw [Real.Angle.sign, sign_eq_one_iff]
  by_contra! hh
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg dist_nonneg dist_nonneg) hh)) h


def Geo (a b c d : ℝ²) (A : ℝ) : Prop :=
  IsCcwConvexPolygon ![a,b,c,d] ∧
    dist a b * dist b c * (∡ a b c).sin = A ∧
    (line[ℝ,a,b] ∥ line[ℝ,c,d] ∧ line[ℝ,a,d] ∥ line[ℝ,b,c])

private theorem parallel_of_sub {a b c d : ℝ²} (h : a-b = -(c-d)) :
    line[ℝ,a,b] ∥ line[ℝ,c,d] := by
  rw [AffineSubspace.affineSpan_pair_parallel_iff_vectorSpan_eq,vectorSpan_pair,vectorSpan_pair]
  change ℝ ∙ (a-b) = ℝ ∙ (c-d)
  rw [h]
  simpa using (Submodule.span_neg (R := ℝ) ({c-d} : Set ℝ²))

theorem geo_corners (x y u v s t A : ℝ) (ha : 0<A) (he : -2*(u*t-v*s)=A) :
    Geo (pt (x+u) (y+v)) (pt (x+s) (y+t)) (pt (x-u) (y-v)) (pt (x-s) (y-t)) A := by
  let a := pt (x+u) (y+v)
  let b := pt (x+s) (y+t)
  let c := pt (x-u) (y-v)
  let d := pt (x-s) (y-t)
  change Geo a b c d A
  have hsum : a+c=b+d := by
    ext i
    fin_cases i <;> simp [a,b,c,d,pt]
  refine ⟨?_,?_,parallel_of_sub (a := a) (b := b) (c := c) (d := d) (by linear_combination (norm := abel) hsum),?_⟩
  · rw [isCcwConvexPolygon_four]
    refine ⟨corner_sign ?_,corner_sign ?_,corner_sign ?_,corner_sign ?_⟩ <;>
      rw [area_coordinates] <;> simp [a,b,c,d,pt] <;> nlinarith
  · rw [area_coordinates]; simp [a,b,c,pt]; nlinarith
  · have hh := parallel_of_sub (a := a) (b := d) (c := c) (d := b) (by linear_combination (norm := abel) hsum)
    simpa [Set.pair_comm c b] using hh

end
end E189

/- Apply incidence mixing at the opposite diagonals through a common centre. -/
open Finset Affine EuclideanGeometry
open scoped BigOperators Real
namespace E189
noncomputable section

abbrev World := ℝ × ℝ × ℝ

def world (m : AffAv) : Shear World where
  toAv := m.toAv.prod (m.toAv.prod m.toAv)
  U a w := (w.1+a,w.2)
  addU a b w := by simp [add_assoc,add_comm a b]
  zeroU w := by simp
  invU a {f} h := by
    change m (fun b => m (fun x => m (fun y => f (b+a,x,y)))) = _
    obtain ⟨C,hC⟩ := h
    exact m.shift a (f := fun b => m (fun x => m (fun y => f (b,x,y))))
      ⟨C,fun b => m.toAv.bound (fun x => m.toAv.bound (fun y => hC (b,x,y)))⟩

def pairObs {n : ℕ} (χ : ℝ² → Fin n) (i : Fin n) (r : ℝ) (w : World) : ℝ :=
  if r ≠ 0 ∧ χ (pt (w.2.1+w.1/r) (w.2.2+1/r))=i ∧ χ (pt (w.2.1-w.1/r) (w.2.2-1/r))=i
  then 1 else 0

theorem pair01 {n : ℕ} (χ : ℝ² → Fin n) (i : Fin n) (r : ℝ) (w : World) :
    0 ≤ pairObs χ i r w ∧ pairObs χ i r w ≤ 1 := by
  unfold pairObs;split <;> norm_num

def Hit {n : ℕ} (χ : ℝ² → Fin n) (i : Fin n) (A : ℝ) : Prop :=
  ∃ a b c d, {a,b,c,d} ⊆ χ⁻¹' {i} ∧ Geo a b c d A

theorem avoid_pair {n : ℕ} (χ : ℝ² → Fin n) (i : Fin n) {A : ℝ} (ha : 0 < A)
    (no : ¬ Hit χ i A) (m : AffAv) (r s : ℝ) (w : World) :
    pairObs χ i r ((world m).U ((-A/2)*r*s) w) * pairObs χ i s w = 0 := by
  rcases w with ⟨b,x,y⟩
  unfold pairObs
  split_ifs with h1 h2 <;> try norm_num
  exfalso
  apply no
  let u := (b+(-A/2)*r*s)/r
  let v := 1/r
  let q := b/s
  let t := 1/s
  obtain ⟨hr,hp,hn⟩ := h1
  obtain ⟨hs,hq,hm⟩ := h2
  refine ⟨pt (x+u) (y+v),pt (x+q) (y+t),pt (x-u) (y-v),pt (x-q) (y-t),?_,
    geo_corners _ _ _ _ _ _ _ ha ?_⟩
  · simp only [Set.insert_subset_iff,Set.singleton_subset_iff,Set.mem_preimage,Set.mem_singleton_iff]
    exact ⟨hp,hq,hn,hm⟩
  · dsimp [u,v,q,t];field_simp;ring

/-- A pair from the finite pigeonhole configuration, recentered at its midpoint. -/
def moved {n : ℕ} (χ : ℝ² → Fin n) (i : Fin n) (j l : ℝ) (v : ℝ × World) :=
  pairObs χ i (v.1/(j-l)) (v.2.1,v.2.2.1+(j+l)*v.2.1/v.1,v.2.2.2+(j+l)/v.1)

theorem translate_center {n : ℕ} (m : AffAv) (χ : ℝ² → Fin n) (i : Fin n) (j l r b : ℝ) :
    m (fun x => m (fun y => moved χ i j l (r,b,x,y))) =
    m (fun x => m (fun y => pairObs χ i (r/(j-l)) (b,x,y))) := by
  let f := fun x y => pairObs χ i (r/(j-l)) (b,x,y)
  let u := (j+l)*b/r
  let v := (j+l)/r
  change m (fun x => m (fun y => f (x+u) (y+v))) = m (fun x => m (f x))
  have h (x) : Bd (f x) := bound01 (fun y => pair01 _ _ _ _)
  have e (x) := m.shift v (h (x+u))
  simp only [e]
  exact m.shift u (f := fun x => m (f x)) (bound01 (fun x => unit_av m.toAv (fun y => pair01 χ i (r/(j-l)) (b,x,y))))

theorem moved_mean {n : ℕ} (m : AffAv) (χ : ℝ² → Fin n) (i : Fin n) (j l : ℝ)
    (no : m (fun r => (world m).eval (pairObs χ i r)) ≤ 0) :
    (m.toAv.prod (world m).toAv) (moved χ i j l) ≤ 0 := by
  change m (fun r => m (fun b => m (fun x => m (fun y => moved χ i j l (r,b,x,y))))) ≤ 0
  simp_rw [translate_center]
  let f := fun r => (world m).eval (pairObs χ i r)
  change m (fun r => f (r/(j-l))) ≤ 0
  by_cases eq : j=l
  · subst l
    have h0 : f 0 = 0 := by
      have e : pairObs χ i 0 = fun _ => 0 := by funext w; simp [pairObs]
      change (world m).eval (pairObs χ i 0) = 0
      rw [e,(world m).toAv.const]
    simp [h0,m.toAv.const]
  · have h := m.dil (inv_ne_zero (sub_ne_zero.mpr eq)) (f := f) (bound01 (fun r => unit_av (world m).toAv (pair01 χ i r)))
    change m (fun x => f ((j-l)⁻¹*x)) = m f at h
    rw [show (fun r => f (r/(j-l))) = (fun r => f ((j-l)⁻¹*r)) from by funext r; rw [div_eq_inv_mul],h]
    exact no

theorem moved_hit {n : ℕ} (χ : ℝ² → Fin n) (r b x y : ℝ) (hr : r ≠ 0) :
    ∃ i : Fin n, ∃ j l : Fin (n+1), moved χ i j.val l.val (r,b,x,y)=1 := by
  let col := fun j : Fin (n+1) => χ (pt (x+2*j.val*b/r) (y+2*j.val/r))
  obtain ⟨j,l,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt col (by simp)
  refine ⟨col j,j,l,?_⟩
  have d : (j.val:ℝ)-(l.val:ℝ) ≠ 0 := sub_ne_zero.mpr (by
    intro h; apply hne; apply Fin.ext; exact_mod_cast h)
  unfold moved pairObs
  dsimp only
  rw [if_pos]
  refine ⟨div_ne_zero hr d,?_,?_⟩
  · change χ (pt _ _) = χ (pt _ _)
    congr 2 <;> field_simp <;> ring
  · rw [he]
    change χ (pt _ _) = χ (pt _ _)
    congr 2 <;> field_simp <;> ring

theorem some_hit {n : ℕ} (χ : ℝ² → Fin n) (A : Fin n → ℝ) (hA : ∀ i,0<A i) :
    ∃ i, Hit χ i (A i) := by
  classical
  by_contra! no
  let m := Classical.choice aff_mean
  let z := world m
  have zero (i) := incidence z m (pairObs χ i) (pair01 χ i)
    (c := -A i / 2) (by have := hA i;linarith) (avoid_pair χ i (hA i) (no i) m)
  let M := m.toAv.prod z.toAv
  let idx := Fin n × Fin (n+1) × Fin (n+1)
  let F := fun (i : idx) => moved χ i.1 i.2.1.val i.2.2.val
  have non (i : idx) (v) : 0 ≤ F i v ∧ F i v ≤ 1 := pair01 .. 
  have lower (v : ℝ × World) : 1-atom 0 v.1 ≤ ∑ i, F i v := by
    rcases v with ⟨r,b,x,y⟩
    by_cases hr : r=0
    · subst r
      simpa [atom] using (sum_nonneg (s := univ) (fun i _ => (non i (0,b,x,y)).1))
    · obtain ⟨i,j,l,h⟩ := moved_hit χ r b x y hr
      let k : idx := (i,j,l)
      have hk : F k (r,b,x,y) = 1 := h
      simpa [atom,hr,hk] using (Finset.single_le_sum (f := fun i => F i (r,b,x,y))
        (fun a _ => (non a _).1) (mem_univ k))
  have H := M.mono ((bd_const 1).sub ((batom 0).comp Prod.fst)) (bd_sum univ F (fun i _ => bound01 (non i))) lower
  rw [M.sub (bd_const 1) ((batom 0).comp Prod.fst),M.const,M.sum _ _ (fun i _ => bound01 (non i))] at H
  have sp : M (fun x : ℝ × World => atom 0 x.1) = 0 := by
    change m (fun r => z.eval (fun _ => atom 0 r)) = 0
    simp only [z.toAv.const,atom_zero]
  have up : ∑ i, M (F i) ≤ 0 := sum_nonpos (fun i _ => moved_mean m χ _ _ _ (zero i.1))
  rw [sp] at H
  linarith

theorem positive : Erdos189.Erdos189For
    (fun a b c d ↦ line[ℝ,a,b] ∥ line[ℝ,c,d] ∧ line[ℝ,a,d] ∥ line[ℝ,b,c])
    (fun a b c _ ↦ dist a b * dist b c * (∡ a b c).sin) := by
  intro n hn χ
  by_contra! no
  choose A hA hno using no
  obtain ⟨i,a,b,c,d,col,poly,area,lines⟩ := some_hit χ A hA
  exact hno i a b c d col poly area lines.1 lines.2

end
end E189

theorem OMA.disproof : ¬ (type_of% @Erdos189.erdos_189.variants.parallelogram) :=
  fun h => h E189.positive
