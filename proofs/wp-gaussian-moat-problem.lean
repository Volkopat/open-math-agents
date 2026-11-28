import OMAStatements.S_wp_gaussian_moat_problem
import Mathlib

/-!
Refutation of the Gaussian moat walk statement.

The mathematical development below is the Lean formalization by OpenAI
(github.com/openai/math, directory lean/OAI/NumberTheory/GaussianMoat), released under the
Apache License 2.0. It is ported here to this older Mathlib with small edits (lemma renames,
attribute and whitespace changes, shortened identifiers) and concatenated into one file.
The final theorem is glue code connecting the OpenAI endpoint to the catalogue statement.
-/

section
namespace OAI
theorem dO {α:Sort _} {c:Prop} {_:Decidable c} {a b:α} (h:c) :
    (if c then a else b) = a:=if_pos h
theorem gR {α:Sort _} {c:Prop} {_:Decidable c} {a b:α} (h:¬c) :
    (if c then a else b) = b:=if_neg h
theorem JG {α:Sort _} {c:Prop} {_:Decidable c} {a:c → α} {b:¬c → α} (h:c) :
    (if hc:c then a hc else b hc) = a h:=dif_pos h
theorem O7 {α:Sort _} {c:Prop} {_:Decidable c} {a:c → α} {b:¬c → α} (h:¬c) :
    (if hc:c then a hc else b hc) = b h:=dif_neg h
namespace GaussianMoat
abbrev jO:={z:GaussianInt // Irreducible z}
noncomputable def rP (D:ℝ):SimpleGraph jO where
  Adj p q:=p ≠ q ∧ dist (p.val:ℂ) (q.val:ℂ) ≤ D
  symm:=by
    constructor
    intro p q h
    exact ⟨h.1.symm,by simpa only [dist_comm] using h.2⟩
  loopless:=by
    constructor
    intro p h
    exact h.1 rfl
def component (D:ℝ) (p:jO):Set jO :=
  {q | (rP D).Reachable p q}
def MainEndpoint:Prop :=
  ∀ (D:ℝ) (z:ℕ → GaussianInt),
    (∀ t,Irreducible (z t)) → Function.Injective z →
    (∀ t,dist (z (t + 1):ℂ) (z t:ℂ) ≤ D) → False
def CQ:Prop :=
  ∀ D:ℝ,∃ B:ℕ,
    (∀ p:jO,(component D p).Finite ∧ (component D p).ncard ≤ B) ∧
    (∀ (n:ℕ) (z:Fin n → GaussianInt),
      (∀ i,Irreducible (z i)) → Function.Injective z →
      (∀ i j:Fin n,j.val = i.val + 1 → dist (z j:ℂ) (z i:ℂ) ≤ D) →
      n ≤ B)
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
def determinant (z w:GaussianInt):ℤ:=z.re * w.im - z.im * w.re
theorem Fv (a z w:GaussianInt) :
    determinant (a * z) (a * w) = a.norm * determinant z w:=by
  simp only [determinant,Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.norm]
  ring
theorem Fw {a z w:GaussianInt} (hz:a ∣ z) (hw:a ∣ w) :
    a.norm ∣ determinant z w:=by
  obtain ⟨u,rfl⟩:=hz
  obtain ⟨v,rfl⟩:=hw
  rw [Fv]
  exact dvd_mul_right _ _
theorem oC {a z w:GaussianInt}
    (hz:a ∣ z) (hw:a ∣ w) (jd:|determinant z w| < a.norm) :
    determinant z w = 0:=by
  by_contra hne
  have hpos:0 < |determinant z w|:=abs_pos.mpr hne
  have hdiv:a.norm ∣ |determinant z w|:=(dvd_abs _ _).mpr (Fw hz hw)
  have hle:=Int.le_of_dvd hpos hdiv
  omega
structure aE where
  primes:Finset ℕ
  factor:ℕ → GaussianInt
  iF:∀ p ∈ primes,Nat.Prime p
  Fy:∀ p ∈ primes,p % 4 = 1
  jA:∀ p ∈ primes,Irreducible (factor p)
  jc:∀ p ∈ primes,(factor p).norm = (p:ℤ)
def aE.avoiding (s:aE):Set GaussianInt :=
  {z | ∀ p ∈ s.primes,¬s.factor p ∣ z ∧ ¬star (s.factor p) ∣ z}
def kD:Prop :=
  ∀ D:ℝ,1 ≤ D → ∃ s:aE,
    ∀ z:ℕ → GaussianInt,(∀ t,z t ∈ s.avoiding) → Function.Injective z →
      (∀ t,dist (z (t + 1):ℂ) (z t:ℂ) ≤ D) → False
theorem Nb (N:ℤ) :
    {z:GaussianInt | |z.re| ≤ N ∧ |z.im| ≤ N}.Finite:=by
  have hinj:Function.Injective (fun z:GaussianInt=>(z.re,z.im)):=by
    intro z w h
    exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hf:=(Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)
  apply (hf.preimage hinj.injOn).subset
  intro z hz
  exact ⟨abs_le.mp hz.1,abs_le.mp hz.2⟩
theorem Oe (N:ℤ):{z:GaussianInt | z.norm ≤ N}.Finite:=by
  apply (Nb (|N| + 1)).subset
  intro z hz
  have heq:z.norm = z.re ^ 2 + z.im ^ 2:=by
    simp only [Zsqrtd.norm]
    ring
  have hn:N ≤ |N|:=le_abs_self N
  have hn0:0 ≤ |N|:=abs_nonneg N
  have hx:z.re ^ 2 ≤ (|N| + 1)^2:=by
    change z.norm ≤ N at hz
    nlinarith [sq_nonneg z.im,sq_nonneg (|N|:ℤ)]
  have hy:z.im ^ 2 ≤ (|N| + 1)^2:=by
    change z.norm ≤ N at hz
    nlinarith [sq_nonneg z.re,sq_nonneg (|N|:ℤ)]
  exact ⟨abs_le_of_sq_le_sq hx (by omega),abs_le_of_sq_le_sq hy (by omega)⟩
theorem mD (a:GaussianInt) (ha:Irreducible a) :
    {z:GaussianInt | Irreducible z ∧ a ∣ z}.Finite:=by
  apply (Oe a.norm).subset
  intro z hz
  exact (Zsqrtd.norm_eq_of_associated (by decide) (ha.associated_of_dvd hz.1 hz.2)).ge
def aE.exceptions (s:aE):Set GaussianInt :=
  {z | Irreducible z ∧ z ∉ s.avoiding}
theorem aE.pW (s:aE):s.exceptions.Finite:=by
  have uO (p:ℕ) (hp:p ∈ s.primes) :
      {z:GaussianInt | Irreducible z ∧
        (s.factor p ∣ z ∨ star (s.factor p) ∣ z)}.Finite:=by
    have Wz:Irreducible (star (s.factor p)) :=
      (MulEquiv.irreducible_iff (starRingAut:RingAut GaussianInt)).mpr
        (s.jA p hp)
    simpa only [← Set.ofPred_or,and_or_left] using
      (mD (s.factor p) (s.jA p hp)).union
        (mD (star (s.factor p)) Wz)
  apply ((s.primes.finite_toSet).biUnion uO).subset
  intro z hz
  obtain ⟨U4,Rr⟩:=hz
  simp only [aE.avoiding,Set.mem_ofPred_eq,not_forall,not_and,not_not] at Rr
  obtain ⟨p,hp,hdiv⟩:=Rr
  exact Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hp,⟨U4,by tauto⟩⟩⟩
theorem aE.Iv (s:aE) (z:ℕ → GaussianInt)
    (hz:∀ t,Irreducible (z t)) (hinj:Function.Injective z) :
    ∃ N:ℕ,∀ t,N ≤ t → z t ∈ s.avoiding:=by
  have hf:(z ⁻¹' s.exceptions).Finite:=s.pW.preimage hinj.injOn
  obtain ⟨N,hN⟩:=hf.exists_le
  refine ⟨N + 1,?_⟩
  intro t ht
  by_contra h
  have ht':t ∈ z ⁻¹' s.exceptions:=⟨hz t,h⟩
  have:=hN t ht'
  omega
theorem Iw (Eb:kD):MainEndpoint:=by
  intro D z hz hinj hstep
  obtain ⟨s,hs⟩:=Eb (max D 1) (le_max_right _ _)
  obtain ⟨N,hN⟩:=s.Iv z hz hinj
  apply hs (fun t=>z (N + t))
  · intro t
    exact hN _ (Nat.le_add_right _ _)
  · exact hinj.comp (fun _ _ h=>Nat.add_left_cancel h)
  · intro t
    have hh:dist (z (N + (t + 1)):ℂ) (z (N + t):ℂ) ≤ D:=by
      simpa only [Nat.add_assoc] using hstep (N + t)
    exact hh.trans (le_max_left _ _)
theorem tL (z:GaussianInt):(z.norm:ℝ) = ‖(z:ℂ)‖ ^ 2:=by
  rw [GaussianInt.intCast_real_norm,Complex.normSq_eq_norm_sq]
theorem o8 (c:GaussianInt) (D:ℝ) :
    {z:GaussianInt | dist (z:ℂ) (c:ℂ) ≤ D}.Finite:=by
  let N:ℤ:=⌈D + ‖(c:ℂ)‖⌉
  apply (Nb N).subset
  intro z hz
  change dist (z:ℂ) (c:ℂ) ≤ D at hz
  have htri:‖(z:ℂ)‖ ≤ dist (z:ℂ) (c:ℂ) + ‖(c:ℂ)‖:=by
    simpa only [sub_add_cancel,← dist_eq_norm] using
      norm_add_le ((z:ℂ) - (c:ℂ)) (c:ℂ)
  have hnorm:‖(z:ℂ)‖ ≤ (N:ℝ):=by
    calc
      ‖(z:ℂ)‖ ≤ dist (z:ℂ) (c:ℂ) + ‖(c:ℂ)‖:=htri
      _ ≤ D + ‖(c:ℂ)‖:=add_le_add_left hz _
      _ ≤ (N:ℝ):=Int.le_ceil _
  constructor
  · have h:=(Complex.abs_re_le_norm (z:ℂ)).trans hnorm
    rw [← GaussianInt.intCast_re,← Int.cast_abs] at h
    exact Int.cast_le.mp h
  · have h:=(Complex.abs_im_le_norm (z:ℂ)).trans hnorm
    rw [← GaussianInt.intCast_im,← Int.cast_abs] at h
    exact Int.cast_le.mp h
theorem Ec {a z:GaussianInt} (hz:z ≠ 0) (h:a ∣ z) :
    a.norm ≤ z.norm:=by
  obtain ⟨w,rfl⟩:=h
  have hw:w ≠ 0:=by
    intro h
    apply hz
    rw [h,mul_zero]
  have hpos:0 < w.norm:=GaussianInt.norm_pos.mpr hw
  rw [Zsqrtd.norm_mul]
  nlinarith [GaussianInt.norm_nonneg a]
theorem yT {a z w:GaussianInt} (hzw:z ≠ w)
    (j6:dist (z:ℂ) (w:ℂ) ^ 2 < (a.norm:ℝ)):¬a ∣ z - w:=by
  intro hdiv
  have hnorm:=Ec (sub_ne_zero.mpr hzw) hdiv
  have hreal:(a.norm:ℝ) ≤ ((z - w).norm:ℝ):=by exact_mod_cast hnorm
  rw [tL (z - w),GaussianInt.toComplex_sub,← dist_eq_norm] at hreal
  exact (not_lt_of_ge hreal) j6
noncomputable def dM (A:Set GaussianInt) (D:ℝ):SimpleGraph GaussianInt where
  Adj z w:=z ≠ w ∧ z ∈ A ∧ w ∈ A ∧ dist (z:ℂ) (w:ℂ) ≤ D
  symm:=by
    constructor
    intro z w h
    exact ⟨h.1.symm,h.2.2.1,h.2.1,by simpa only [dist_comm] using h.2.2.2⟩
  loopless:=by
    constructor
    intro z h
    exact h.1 rfl
theorem zW {A:Set GaussianInt} {D:ℝ} {z w:GaussianInt}
    (p:(dM A D).Walk z w) (hz:z ∈ A) (i:ℕ):p.getVert i ∈ A:=by
  induction p generalizing i with
  | nil=>simpa using hz
  | @cons u v w huv p ih =>
    cases i with
    | zero=>simpa using hz
    | succ i=>exact ih huv.2.2.1 i
theorem KX {A:Set GaussianInt} {D:ℝ} {z w:GaussianInt}
    (p:(dM A D).Walk z w) :
    dist (z:ℂ) (w:ℂ) ≤ (p.length:ℝ) * max D 0:=by
  induction p with
  | nil=>simp
  | @cons u v w huv p ih =>
    calc
      dist (u:ℂ) (w:ℂ) ≤ dist (u:ℂ) (v:ℂ) + dist (v:ℂ) (w:ℂ) :=
        dist_triangle _ _ _
      _ ≤ D + (p.length:ℝ) * max D 0:=add_le_add huv.2.2.2 ih
      _ ≤ ((p.cons huv).length:ℝ) * max D 0:=by
        simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith [le_max_left D 0]
structure fF (A:Set GaussianInt) (D:ℝ) (root:GaussianInt) (n:ℕ) where
  point:Fin (n + 1) → GaussianInt
  mem:∀ i,point i ∈ A
  start:point 0 = root
  injective:Function.Injective point
  step:∀ i j,j.val = i.val + 1 → dist (point j:ℂ) (point i:ℂ) ≤ D
theorem fF.ext {A:Set GaussianInt} {D:ℝ} {root:GaussianInt} {n:ℕ}
    {p q:fF A D root n} (h:p.point = q.point):p = q:=by
  cases p; cases q; subst h; rfl
theorem fF.dist_le {A:Set GaussianInt} {D:ℝ} {root:GaussianInt}
    {n:ℕ} (p:fF A D root n) (i:Fin (n + 1)) :
    dist (p.point i:ℂ) (root:ℂ) ≤ (i.val:ℝ) * max D 0:=by
  induction i using Fin.induction with
  | zero=>simp [p.start]
  | succ i ih =>
    calc
      dist (p.point i.succ:ℂ) (root:ℂ) ≤
          dist (p.point i.succ:ℂ) (p.point i.castSucc:ℂ) +
            dist (p.point i.castSucc:ℂ) (root:ℂ):=dist_triangle _ _ _
      _ ≤ D + (i.val:ℝ) * max D 0:=add_le_add (p.step _ _ rfl) ih
      _ ≤ (i.succ.val:ℝ) * max D 0:=by
        simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
        nlinarith [le_max_left D 0]
instance fF.finite (A:Set GaussianInt) (D:ℝ) (root:GaussianInt) (n:ℕ) :
    Finite (fF A D root n):=by
  let S:Set (Fin (n + 1) → GaussianInt) :=
    {f | ∀ i,dist (f i:ℂ) (root:ℂ) ≤ (n:ℝ) * max D 0}
  have hS:S.Finite:=Set.Finite.pi' (fun _=>o8 root ((n:ℝ) * max D 0))
  let:=hS.to_subtype
  let f:fF A D root n → S:=fun p=>⟨p.point,fun i =>
    (p.dist_le i).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt) (le_max_right D 0))⟩
  exact Finite.of_injective f (fun p q h=>fF.ext (congrArg Subtype.val h))
def fF.restrict {A:Set GaussianInt} {D:ℝ} {root:GaussianInt}
    {n m:ℕ} (h:n ≤ m) (p:fF A D root m):fF A D root n where
  point i:=p.point (Fin.castLE (by omega) i)
  mem i:=p.mem _
  start:=by simpa using p.start
  injective:=p.injective.comp (Fin.castLE_injective (by omega))
  step i j hij:=p.step _ _ hij
theorem vI {A:Set GaussianInt} {D:ℝ} {root:GaussianInt}
    (hroot:root ∈ A) (SI:{w | (dM A D).Reachable root w}.Infinite) :
    ∃ z:ℕ → GaussianInt,(∀ n,z n ∈ A) ∧ Function.Injective z ∧
      ∀ n,dist (z (n + 1):ℂ) (z n:ℂ) ≤ D:=by
  classical
  have hne (n:ℕ):Nonempty (fF A D root n):=by
    have hnot:¬ {w | (dM A D).Reachable root w} ⊆
        {w | dist (w:ℂ) (root:ℂ) ≤ (n:ℝ) * max D 0}:=by
      intro h
      exact SI ((o8 root ((n:ℝ) * max D 0)).subset h)
    obtain ⟨w,hw,XF⟩:=Set.not_subset.mp hnot
    apply hw.elim_path
    intro path
    let p:=path.val
    have hn:n ≤ p.length:=by
      by_contra hn
      have hlen:(p.length:ℝ) ≤ (n:ℝ):=by exact_mod_cast (by omega:p.length ≤ n)
      have hdist:=(KX p).trans
        (mul_le_mul_of_nonneg_right hlen (le_max_right D 0))
      apply XF
      change dist (w:ℂ) (root:ℂ) ≤ (n:ℝ) * max D 0
      simpa only [dist_comm] using hdist
    exact ⟨{
      point:=fun i=>p.getVert i.val
      mem:=fun i=>zW p hroot _
      start:=p.getVert_zero
      injective:=fun i j h=>Fin.ext (path.isPath.getVert_injOn
        (show i.val ≤ p.length from (Nat.le_of_lt_succ i.isLt).trans hn)
        (show j.val ≤ p.length from (Nat.le_of_lt_succ j.isLt).trans hn) h)
      step:=fun i j h=>by
        have hadj:=p.adj_getVert_succ (i:=i.val) (by omega)
        simpa only [h,dist_comm] using hadj.2.2.2
    }⟩
  let (n:ℕ):Nonempty (fF A D root n):=hne n
  obtain ⟨p,hp⟩:=exists_seq_forall_proj_of_forall_finite
    (α:=fun n=>fF A D root n)
    (fun h=>fF.restrict h)
    (by intro n a; apply fF.ext; funext i; rfl)
    (by intro i j k hij hjk a; apply fF.ext; funext l; rfl)
    (fun _ _=>Set.toFinite _)
  let z:ℕ → GaussianInt:=fun n=>(p n).point (Fin.last n)
  have hagree (n k:ℕ) (hnk:n ≤ k) :
      (p k).point ⟨n,by omega⟩ = z n:=by
    simpa only [fF.restrict,z,Fin.last,Fin.castLE] using
      congrArg (fun a:fF A D root n=>a.point (Fin.last n)) (hp hnk)
  refine ⟨z,fun n=>(p n).mem _,?_,?_⟩
  · intro n m heq
    have h:=(hagree n (max n m) (le_max_left _ _)).trans
      (heq.trans (hagree m (max n m) (le_max_right _ _)).symm)
    exact congrArg Fin.val ((p (max n m)).injective h)
  · intro n
    have h:=(p (n + 1)).step ⟨n,by omega⟩ (Fin.last (n + 1)) rfl
    simpa only [hagree n (n + 1) (by omega)] using h
theorem zX {A:Set GaussianInt} {D:ℝ}
    (hno:∀ z:ℕ → GaussianInt,(∀ n,z n ∈ A) → Function.Injective z →
      (∀ n,dist (z (n + 1):ℂ) (z n:ℂ) ≤ D) → False)
    {root:GaussianInt} (hroot:root ∈ A) :
    {w | (dM A D).Reachable root w}.Finite:=by
  by_contra h
  obtain ⟨z,hz,hinj,hstep⟩:=vI hroot h
  exact hno z hz hinj hstep
def JH {A:Set GaussianInt} {D:ℝ} (v:GaussianInt)
    (hv:∀ z ∈ A,z + v ∈ A) :
    dM A D →g dM A D where
  toFun z:=z + v
  map_rel':=by
    intro z w h
    refine ⟨fun he=>h.1 (add_right_cancel he),hv z h.2.1,hv w h.2.2.1,?_⟩
    simpa only [map_add,dist_add_right] using h.2.2.2
theorem s8 {A:Set GaussianInt} {D:ℝ}
    {root x y v:GaussianInt}
    (hfinite:{w | (dM A D).Reachable root w}.Finite)
    (hx:(dM A D).Reachable root x)
    (hy:(dM A D).Reachable root y)
    (hv:∀ z ∈ A,z + v ∈ A) (hxy:y = x + v):x = y:=by
  classical
  by_contra hne
  have hv0:v ≠ 0:=by intro h; apply hne; simpa [h] using hxy.symm
  have hreach:(dM A D).Reachable x (x + v):=by
    rw [← hxy]
    exact hx.symm.trans hy
  have hall (n:ℕ):(dM A D).Reachable x (x + n • v):=by
    induction n with
    | zero=>simp
    | succ n ih =>
      have ht:=ih.map (JH v hv)
      have hh:=hreach.trans ht
      change (dM A D).Reachable x ((x + n • v) + v) at hh
      simpa only [succ_nsmul,add_assoc] using hh
  have hinj:Function.Injective (fun n:ℕ=>x + n • v):=by
    intro n m h
    have hh:=add_left_cancel h
    simp only [nsmul_eq_mul] at hh
    exact Nat.cast_injective (mul_right_cancel₀ hv0 hh)
  apply (Set.infinite_range_of_injective hinj)
  exact hfinite.subset (by rintro _ ⟨n,rfl⟩; exact hx.trans (hall n))
def aE.period (s:aE):ℕ:=∏ p ∈ s.primes,p
theorem aE.period_pos (s:aE):0 < s.period:=by
  exact Finset.prod_pos (fun p hp=>(s.iF p hp).pos)
theorem aE.KY (s:aE) {p:ℕ} (hp:p ∈ s.primes) :
    s.factor p ∣ (s.period:GaussianInt) ∧ star (s.factor p) ∣ (s.period:GaussianInt):=by
  have hn:(p:GaussianInt) = s.factor p * star (s.factor p):=by
    rw [← Zsqrtd.norm_eq_mul_conj,s.jc p hp]
    simp
  have hd:(p:GaussianInt) ∣ (s.period:GaussianInt):=by
    have hh:p ∣ s.period:=Finset.dvd_prod_of_mem (fun p:ℕ=>p) hp
    exact map_dvd (Nat.castRingHom GaussianInt) hh
  constructor
  · apply dvd_trans _ hd
    rw [hn]
    exact dvd_mul_right _ _
  · apply dvd_trans _ hd
    rw [hn]
    exact dvd_mul_left _ _
theorem aE.periodic (s:aE) (z v:GaussianInt) (hz:z ∈ s.avoiding) :
    z + (s.period:GaussianInt) * v ∈ s.avoiding:=by
  intro p hp
  have hd:=s.KY hp
  constructor
  · intro h
    apply (hz p hp).1
    have hh:=dvd_sub h (dvd_mul_of_dvd_left hd.1 v)
    simpa only [add_sub_cancel_right] using hh
  · intro h
    apply (hz p hp).2
    have hh:=dvd_sub h (dvd_mul_of_dvd_left hd.2 v)
    simpa only [add_sub_cancel_right] using hh
def residue (Q:ℕ) (z:GaussianInt):ZMod Q × ZMod Q:=(z.re,z.im)
theorem vN {Q:ℕ} {x y:GaussianInt}
    (h:residue Q x = residue Q y) :
    ∃ v:GaussianInt,y = x + (Q:GaussianInt) * v:=by
  have hx:=(ZMod.intCast_eq_intCast_iff_dvd_sub x.re y.re Q).mp (congrArg Prod.fst h)
  have hy:=(ZMod.intCast_eq_intCast_iff_dvd_sub x.im y.im Q).mp (congrArg Prod.snd h)
  obtain ⟨a,ha⟩:=hx
  obtain ⟨b,hb⟩:=hy
  refine ⟨⟨a,b⟩,?_⟩
  ext <;> simp only [Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_mul,Zsqrtd.im_mul,
    Zsqrtd.re_natCast,Zsqrtd.im_natCast,zero_mul,mul_zero,add_zero] <;> omega
theorem zY {A:Set GaussianInt} {D:ℝ} {Q:ℕ} (hQ:Q ≠ 0)
    (U5:∀ z ∈ A,∀ v:GaussianInt,z + (Q:GaussianInt) * v ∈ A)
    {root:GaussianInt}
    (hfinite:{w | (dM A D).Reachable root w}.Finite) :
    {w | (dM A D).Reachable root w}.ncard ≤ Q ^ 2:=by
  classical
  let:NeZero Q:=⟨hQ⟩
  let C:={w | (dM A D).Reachable root w}
  have hinj:Set.InjOn (residue Q) C:=by
    intro x hx y hy heq
    obtain ⟨v,hv⟩:=vN heq
    exact s8 hfinite hx hy
      (fun z hz=>U5 z hz v) hv
  have hcard:=Set.ncard_le_card ((residue Q) '' C)
  rw [Set.InjOn.ncard_image hinj,Nat.card_prod,Nat.card_zmod,pow_two] at *
  exact hcard
def aE.boundary (s:aE) (D:ℝ):Set GaussianInt :=
  {z | z ∈ s.avoiding ∧ ∃ e ∈ s.exceptions,dist (z:ℂ) (e:ℂ) ≤ D}
theorem aE.Nc (s:aE) (D:ℝ):(s.boundary D).Finite:=by
  apply (s.pW.biUnion (fun e _=>o8 e D)).subset
  rintro z ⟨_,e,he,hd⟩
  exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,hd⟩⟩
def aE.restored (s:aE) (D:ℝ):Set GaussianInt :=
  s.exceptions ∪ ⋃ v ∈ s.boundary D,{w | (dM s.avoiding D).Reachable v w}
theorem aE.Nd (s:aE) (D:ℝ)
    (hf:∀ r ∈ s.avoiding,{w | (dM s.avoiding D).Reachable r w}.Finite) :
    (s.restored D).Finite:=by
  exact s.pW.union ((s.Nc D).biUnion (fun _ hv=>hf _ hv.1))
theorem q6 {A:Set GaussianInt} {D:ℝ} {r w:GaussianInt}
    (hr:r ∈ A) (h:(dM A D).Reachable r w):w ∈ A:=by
  apply h.elim
  intro p
  simpa only [p.getVert_length] using zW p hr p.length
theorem aE.CX (s:aE) (D:ℝ)
    {p q:jO} (hp:p.val ∈ s.restored D) (hadj:(rP D).Adj p q) :
    q.val ∈ s.restored D:=by
  classical
  by_cases hqa:q.val ∈ s.avoiding
  · rcases hp with hpe | hp
    · exact Or.inr (Set.mem_iUnion.mpr ⟨q.val,Set.mem_iUnion.mpr
        ⟨⟨hqa,p.val,hpe,by simpa only [dist_comm] using hadj.2⟩,
          SimpleGraph.Reachable.refl _⟩⟩)
    · obtain ⟨v,hv⟩:=Set.mem_iUnion.mp hp
      obtain ⟨hvb,hvp⟩:=Set.mem_iUnion.mp hv
      have hpa:=q6 hvb.1 hvp
      have hed:(dM s.avoiding D).Adj p.val q.val :=
        ⟨fun h=>hadj.1 (Subtype.ext h),hpa,hqa,hadj.2⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hvb,
        hvp.trans hed.reachable⟩⟩)
  · exact Or.inl ⟨q.property,hqa⟩
theorem Iz {D:ℝ} {T:Set GaussianInt}
    (hclosed:∀ p q:jO,p.val ∈ T → (rP D).Adj p q → q.val ∈ T)
    {p q:jO} (hp:p.val ∈ T) (h:(rP D).Reachable p q):q.val ∈ T:=by
  apply h.elim
  intro w
  clear h
  induction w with
  | nil=>exact hp
  | @cons a b c hab w ih=>exact ih (hclosed a b hp hab)
theorem lW {A:Set GaussianInt} {D:ℝ} {r:GaussianInt}
    (hr:r ∉ A):{w | (dM A D).Reachable r w} = {r}:=by
  ext w
  constructor
  · intro h
    apply h.elim
    intro p
    cases p with
    | nil=>rfl
    | cons hed p=>exact (hr hed.2.1).elim
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst w
    exact SimpleGraph.Reachable.refl _
theorem aE.LL (s:aE) (D:ℝ) (p:jO) :
    Subtype.val '' component D p ⊆
      {w | (dM s.avoiding D).Reachable p.val w} ∪ s.restored D:=by
  rintro _ ⟨q,hq,rfl⟩
  apply Iz (T :=
    {w | (dM s.avoiding D).Reachable p.val w} ∪ s.restored D) _
    (Or.inl (SimpleGraph.Reachable.refl _)) hq
  intro a b ha hab
  rcases ha with ha | ha
  · by_cases hpa:p.val ∈ s.avoiding
    · by_cases hba:b.val ∈ s.avoiding
      · exact Or.inl (ha.trans (show (dM s.avoiding D).Adj a.val b.val from
          ⟨fun hh=>hab.1 (Subtype.ext hh),q6 hpa ha,hba,hab.2⟩).reachable)
      · exact Or.inr (Or.inl ⟨b.property,hba⟩)
    · have hap:a.val = p.val:=by
        have hh:a.val ∈ {w | (dM s.avoiding D).Reachable p.val w}:=ha
        rw [lW hpa] at hh
        exact hh
      exact Or.inr (s.CX D (Or.inl (by simpa only [hap] using
        (show p.val ∈ s.exceptions from ⟨p.property,hpa⟩))) hab)
  · exact Or.inr (s.CX D ha hab)
theorem rF (Eb:kD) (D:ℝ) :
    ∃ B:ℕ,∀ p:jO,(component D p).Finite ∧ (component D p).ncard ≤ B:=by
  classical
  obtain ⟨s,hs⟩:=Eb (max D 1) (le_max_right _ _)
  have hno:∀ z:ℕ → GaussianInt,(∀ n,z n ∈ s.avoiding) → Function.Injective z →
      (∀ n,dist (z (n + 1):ℂ) (z n:ℂ) ≤ D) → False:=by
    intro z hz hinj hstep
    exact hs z hz hinj (fun n=>(hstep n).trans (le_max_left _ _))
  have hf (r:GaussianInt):{w | (dM s.avoiding D).Reachable r w}.Finite:=by
    by_cases hr:r ∈ s.avoiding
    · exact zX hno hr
    · rw [lW hr]
      exact Set.finite_singleton _
  have hK:=s.Nd D (fun r _=>hf r)
  refine ⟨s.period ^ 2 + (s.restored D).ncard,fun p=>?_⟩
  let C:={w | (dM s.avoiding D).Reachable p.val w}
  have hC:C.ncard ≤ s.period ^ 2:=zY
    (Nat.ne_of_gt s.period_pos) (fun z hz v=>s.periodic z v hz) (hf p.val)
  have hsubset:=s.LL D p
  have SK:=((hf p.val).union hK).subset hsubset
  have hfin:(component D p).Finite:=by
    apply (SK.preimage Subtype.val_injective.injOn).subset
    intro q hq
    exact ⟨q,hq,rfl⟩
  refine ⟨hfin,?_⟩
  have hle:=(Set.ncard_le_ncard hsubset ((hf p.val).union hK)).trans
    (Set.ncard_union_le C (s.restored D))
  rw [Set.InjOn.ncard_image Subtype.val_injective.injOn] at hle
  exact hle.trans (Nat.add_le_add_right hC _)
theorem BH {D:ℝ} {B:ℕ}
    (hB:∀ p:jO,(component D p).Finite ∧ (component D p).ncard ≤ B)
    (n:ℕ) (z:Fin n → GaussianInt) (hz:∀ i,Irreducible (z i))
    (hinj:Function.Injective z)
    (hstep:∀ i j:Fin n,j.val = i.val + 1 → dist (z j:ℂ) (z i:ℂ) ≤ D):n ≤ B:=by
  classical
  cases n with
  | zero=>exact Nat.zero_le _
  | succ n =>
    let f:Fin (n + 1) → jO:=fun i=>⟨z i,hz i⟩
    have hf:Function.Injective f:=fun i j h=>hinj (congrArg Subtype.val h)
    have hreach (i:Fin (n + 1)):(rP D).Reachable (f 0) (f i):=by
      induction i using Fin.induction with
      | zero=>exact SimpleGraph.Reachable.refl _
      | succ i ih =>
        apply ih.trans
        apply SimpleGraph.Adj.reachable
        exact ⟨fun h=>(by have hh:=congrArg Fin.val (hf h); simp at hh),
          by simpa only [dist_comm] using hstep i.castSucc i.succ rfl⟩
    have hsubset:Set.range f ⊆ component D (f 0):=by
      rintro _ ⟨i,rfl⟩
      exact hreach i
    have hle:=(Set.ncard_le_ncard hsubset (hB _).1).trans (hB _).2
    simpa only [Set.ncard_range_of_injective hf,Nat.card_fin] using hle
theorem z4 (Eb:kD):MainEndpoint ∧ CQ:=by
  refine ⟨Iw Eb,fun D=>?_⟩
  obtain ⟨B,hB⟩:=rF Eb D
  exact ⟨B,hB,BH hB⟩
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9
namespace GaussianMoat
def iG (v:GaussianInt):Prop:=IsCoprime v.re v.im
theorem qO {v w:GaussianInt}
    (hv:iG v) (hvw:determinant v w = 0) :
    ∃ a:ℤ,w = (a:GaussianInt) * v:=by
  obtain ⟨r,s,hrs⟩:=hv
  refine ⟨r * w.re + s * w.im,?_⟩
  change v.re * w.im - v.im * w.re = 0 at hvw
  ext <;> simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_intCast,
    Zsqrtd.im_intCast,zero_mul,mul_zero,add_zero]
  · nlinarith [congrArg (fun x:ℤ=>x * w.re) hrs,
      congrArg (fun x:ℤ=>s * x) hvw]
  · nlinarith [congrArg (fun x:ℤ=>x * w.im) hrs,
      congrArg (fun x:ℤ=>r * x) hvw]
theorem wP {w:GaussianInt} (hw:w ≠ 0) :
    ∃ v:GaussianInt,iG v ∧ v ≠ 0 ∧
      ∃ a:ℤ,a ≠ 0 ∧ w = (a:GaussianInt) * v:=by
  have hg:=(Zsqrtd.gcd_pos_iff w).mpr hw
  obtain ⟨v,hv,hcop⟩:=Zsqrtd.exists_coprime_of_gcd_pos hg
  refine ⟨v,hcop,?_,(Int.gcd w.re w.im:ℤ),by exact_mod_cast hg.ne',hv⟩
  intro h
  apply hw
  simp only [h,mul_zero] at hv
  exact hv
theorem O8 {a b:GaussianInt} (h:a ∣ b):a.norm ∣ b.norm:=by
  obtain ⟨u,rfl⟩:=h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _
theorem jP {p:ℕ} {π:GaussianInt} (hp:Nat.Prime p)
    (hπ:π.norm = (p:ℤ)) (a:ℤ):π ∣ (a:GaussianInt) ↔ (p:ℤ) ∣ a:=by
  have hp':Prime (p:ℤ):=Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  constructor
  · intro h
    have hn:=O8 h
    rw [hπ,Zsqrtd.norm_intCast] at hn
    exact (hp'.dvd_mul.mp hn).elim id id
  · intro h
    have hd:π ∣ (p:GaussianInt):=by
      have he:(p:GaussianInt) = π * star π:=by
        rw [← Zsqrtd.norm_eq_mul_conj,hπ]
        simp
      rw [he]
      exact dvd_mul_right _ _
    exact hd.trans (map_dvd (Int.castRingHom GaussianInt) h)
theorem rS {p:ℕ} {π v:GaussianInt}
    (hp:Nat.Prime p) (hpodd:p ≠ 2) (hπ:π.norm = (p:ℤ))
    (hv:iG v):¬ (π ∣ v ∧ star π ∣ v):=by
  rintro ⟨h1,h2⟩
  have hs:π ∣ star v:=by
    obtain ⟨u,hu⟩:=h2
    refine ⟨star u,?_⟩
    simpa only [star_mul,star_star,mul_comm] using congrArg star hu
  have hreal:π ∣ ((2 * v.re:ℤ):GaussianInt):=by
    have heq:((2 * v.re:ℤ):GaussianInt) = v + star v:=by
      ext <;> simp
      ring
    rw [heq]
    exact dvd_add h1 hs
  have WA:π ∣ ((2 * v.im:ℤ):GaussianInt):=by
    have heq:((2 * v.im:ℤ):GaussianInt) =
        (⟨0,-1⟩:GaussianInt) * (v - star v):=by
      ext <;> simp [Zsqrtd.re_mul,Zsqrtd.im_mul]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_sub h1 hs) _
  have hp':Prime (p:ℤ):=Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hp2:¬ (p:ℤ) ∣ 2:=by
    intro h
    have hn:p ∣ 2:=by exact_mod_cast h
    have hh:=(Nat.dvd_prime Nat.prime_two).mp hn
    exact hh.elim hp.ne_one hpodd
  have hr:(p:ℤ) ∣ v.re :=
    (hp'.dvd_mul.mp ((jP hp hπ _).mp hreal)).resolve_left hp2
  have hi:(p:ℤ) ∣ v.im :=
    (hp'.dvd_mul.mp ((jP hp hπ _).mp WA)).resolve_left hp2
  exact hp'.not_isUnit (hv.isUnit_of_dvd' hr hi)
def dG (π:GaussianInt) (b:Bool):GaussianInt:=if b then π else star π
theorem iW (π:GaussianInt) (b:Bool):(dG π b).norm = π.norm:=by
  cases b <;> simp [dG,Zsqrtd.norm_conj]
theorem oD {π:GaussianInt} (hπ:Irreducible π) (b:Bool) :
    Irreducible (dG π b):=by
  cases b
  · exact (MulEquiv.irreducible_iff (starRingAut:RingAut GaussianInt)).mpr hπ
  · exact hπ
theorem rT {p q:ℕ} {π ρ:GaussianInt}
    (hp:Nat.Prime p) (hq:Nat.Prime q) (hpq:p ≠ q)
    (hπ:π.norm = (p:ℤ)) (hρ:ρ.norm = (q:ℤ)):IsCoprime π ρ:=by
  have hc:Nat.Coprime p q:=(hp.coprime_iff_not_dvd).mpr (by
    intro hd
    have hh:=(Nat.dvd_prime hq).mp hd
    exact hh.elim hp.ne_one hpq)
  have hcz:IsCoprime (p:ℤ) (q:ℤ):=by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa using hc
  have hcg:=hcz.map (Int.castRingHom GaussianInt)
  have Yx:π ∣ (p:GaussianInt):=(jP hp hπ _).mpr (dvd_refl _)
  have Yy:ρ ∣ (q:GaussianInt):=(jP hq hρ _).mpr (dvd_refl _)
  exact hcg.of_isCoprime_of_dvd_left Yx |>.of_isCoprime_of_dvd_right Yy
theorem z5 {ι:Type c9} (s:Finset ι) (f:ι → GaussianInt) :
    (∏ i ∈ s,f i).norm = ∏ i ∈ s,(f i).norm:=by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>simp [hi,Zsqrtd.norm_mul,ih]
theorem aE.z6 (s:aE) (t:Finset ℕ) (ht:t ⊆ s.primes)
    (σ:ℕ → Bool) {v:GaussianInt}
    (hd:∀ p ∈ t,dG (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t,dG (s.factor p) (σ p)) ∣ v:=by
  apply Finset.prod_dvd_of_coprime _ hd
  intro p hp q hq hpq
  exact rT (s.iF p (ht hp)) (s.iF q (ht hq)) hpq
    ((iW _ _).trans (s.jc p (ht hp)))
    ((iW _ _).trans (s.jc q (ht hq)))
theorem aE.z7 (s:aE) (t:Finset ℕ)
    (ht:t ⊆ s.primes) (σ:ℕ → Bool) {v:GaussianInt} (hv:v ≠ 0)
    (hd:∀ p ∈ t,dG (s.factor p) (σ p) ∣ v) :
    (∏ p ∈ t,(p:ℤ)) ≤ v.norm:=by
  have hle:=Ec hv (s.z6 t ht σ hd)
  rw [z5] at hle
  convert hle using 1
  apply Finset.prod_congr rfl
  intro p hp
  exact ((iW _ _).trans (s.jc p (ht hp))).symm
open scoped Classical in
theorem aE.pZ (s:aE)
    (t:Finset ℕ) (ht:t ⊆ s.primes) (σ:ℕ → Bool) (v:GaussianInt) (a:ℤ)
    (hw:(∏ p ∈ t,dG (s.factor p) (σ p)) ∣ (a:GaussianInt) * v) :
    (∏ p ∈ t.filter (fun p=>¬ dG (s.factor p) (σ p) ∣ v),(p:ℤ)) ∣ a:=by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    have hp':=s.iF p (ht (Finset.mem_filter.mp hp).1)
    have hq':=s.iF q (ht (Finset.mem_filter.mp hq).1)
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.Coprime p q
    exact (hp'.coprime_iff_not_dvd).mpr (fun h =>
      ((Nat.dvd_prime hq').mp h).elim hp'.ne_one hpq)
  · intro p hp
    obtain ⟨hpt,hpv⟩:=Finset.mem_filter.mp hp
    have hpp:=ht hpt
    have hd:dG (s.factor p) (σ p) ∣ (a:GaussianInt) * v :=
      (Finset.dvd_prod_of_mem _ hpt).trans hw
    have ha:=((oD (s.jA p hpp) (σ p)).prime.dvd_mul.mp hd).resolve_right hpv
    exact (jP (s.iF p hpp)
      ((iW _ _).trans (s.jc p hpp)) a).mp ha
open scoped Classical in
theorem aE.BK (s:aE)
    (t:Finset ℕ) (ht:t ⊆ s.primes) (σ:ℕ → Bool)
    {v w:GaussianInt} (hv:iG v) (hw:w ≠ 0)
    (Nh:determinant v w = 0)
    (hdiv:(∏ p ∈ t,dG (s.factor p) (σ p)) ∣ w) :
    v.norm * (∏ p ∈ t.filter (fun p=>¬ dG (s.factor p) (σ p) ∣ v),(p:ℤ)) ^ 2
      ≤ w.norm:=by
  classical
  obtain ⟨a,rfl⟩:=qO hv Nh
  have ha:a ≠ 0:=by intro h; simp [h] at hw
  have hd:=s.pZ t ht σ v a hdiv
  have habs:0 < |a|:=abs_pos.mpr ha
  have hle:=Int.le_of_dvd habs ((dvd_abs _ _).mpr hd)
  have hprod:0 ≤ ∏ p ∈ t.filter (fun p=>¬ dG (s.factor p) (σ p) ∣ v),(p:ℤ) :=
    Finset.prod_nonneg (fun _ _=>Int.natCast_nonneg _)
  have hs:(∏ p ∈ t.filter (fun p=>¬ dG (s.factor p) (σ p) ∣ v),(p:ℤ)) ^ 2 ≤ a ^ 2:=by
    nlinarith [sq_abs a]
  rw [Zsqrtd.norm_mul,Zsqrtd.norm_intCast]
  nlinarith [mul_le_mul_of_nonneg_left hs (GaussianInt.norm_nonneg v)]
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9
namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable def nL:Measure Bool:=(PMF.uniformOfFintype Bool).toMeasure
instance RD:IsProbabilityMeasure nL:=by
  unfold nL
  infer_instance
noncomputable def gY (ι:Type c9) [Fintype ι]:Measure (ι → Bool) :=
  Measure.pi (fun _=>nL)
instance QV (ι:Type c9) [Fintype ι]:IsProbabilityMeasure (gY ι):=by
  unfold gY
  infer_instance
theorem O9 (f:Bool → ℝ):∫ b,f b ∂nL = (f false + f true) / 2:=by
  have hf:Integrable f nL:=Integrable.of_mem_Icc
    (min (f false) (f true)) (max (f false) (f true)) (by fun_prop) (by
      apply ae_of_all
      intro b
      cases b <;> simp)
  rw [integral_fintype hf]
  simp [nL,measureReal_def,
    PMF.uniformOfFintype_apply]
  ring
theorem Oi {ι:Type c9} [Fintype ι] (f:ι → Bool → ℝ) (w:ι → ℝ)
    (hf:∀ i b,f i b ∈ Set.Icc 0 (w i)) {ε:ℝ} (hε:0 ≤ ε) :
    (gY ι).real {σ | ε + ∑ i,(f i false + f i true) / 2 ≤ ∑ i,f i (σ i)}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i,(((‖w i‖₊ / 2) ^ 2:ℝ≥0):ℝ))):=by
  classical
  let X:ι → (ι → Bool) → ℝ:=fun i σ=>f i (σ i) - (f i false + f i true) / 2
  have hsub (i:ι):HasSubgaussianMGF (X i) ((‖w i‖₊ / 2) ^ 2) (gY ι):=by
    have h:=hasSubgaussianMGF_of_mem_Icc (μ:=nL) (X:=f i)
      (by fun_prop) (ae_of_all _ (hf i))
    rw [O9] at h
    simp only [sub_zero] at h
    have he:=(measurePreserving_eval (fun _:ι=>nL) i).map_eq
    rw [← he] at h
    have heval:AEMeasurable (Function.eval i:(ι → Bool) → Bool) (gY ι) :=
      (measurable_pi_apply i).aemeasurable
    exact HasSubgaussianMGF.of_map heval h
  have hind:iIndepFun X (gY ι) :=
    iIndepFun_pi (X:=fun i b=>f i b - (f i false + f i true) / 2) (fun _=>by fun_prop)
  have h:=HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s:=Finset.univ) (fun i _=>hsub i) hε
  simpa only [X,Finset.sum_sub_distrib,le_sub_iff_add_le,NNReal.coe_sum] using h
open scoped Classical in
noncomputable def aE.eligible (s:aE) (v:GaussianInt):Finset ℕ :=
  s.primes.filter (fun p=>s.factor p ∣ v ∨ star (s.factor p) ∣ v)
noncomputable def aE.jD (s:aE) (v:GaussianInt) (p:ℕ) (b:Bool):ℝ:=by
  classical
  exact if dG (s.factor p) b ∣ v then Real.log p else 0
theorem aE.JI (s:aE) {v:GaussianInt} (hv:v ≠ 0) :
    ∑ p ∈ s.eligible v,Real.log (p:ℝ) ≤ Real.log (v.norm:ℝ):=by
  classical
  let σ:ℕ → Bool:=fun p=>decide (s.factor p ∣ v)
  have hnorm:=s.z7 (s.eligible v)
    (Finset.filter_subset _ _) σ hv (by
      intro p hp
      obtain ⟨_,hleft | hright⟩:=Finset.mem_filter.mp hp
      · simp [σ,dG,hleft]
      · by_cases hd:s.factor p ∣ v
        · simp [σ,dG,hd]
        · simpa [σ,dG,hd] using hright)
  have Vq:∏ p ∈ s.eligible v,(p:ℝ) ≤ (v.norm:ℝ):=by
    have h:((∏ p ∈ s.eligible v,(p:ℤ)):ℝ) ≤ (v.norm:ℝ):=by exact_mod_cast hnorm
    push_cast at h
    exact h
  have hpos (p:ℕ) (hp:p ∈ s.eligible v):0 < (p:ℝ):=by
    exact_mod_cast (s.iF p (Finset.mem_filter.mp hp).1).pos
  have hlog:=Real.log_le_log (Finset.prod_pos hpos) Vq
  rw [Real.log_prod (fun p hp=>(hpos p hp).ne')] at hlog
  exact hlog
theorem aE.Ql (s:aE) {v:GaussianInt}
    (hv:iG v) (hv0:v ≠ 0) :
    ∑ p:s.primes,(s.jD v p false + s.jD v p true) / 2 ≤
      Real.log (v.norm:ℝ) / 2:=by
  classical
  have heq:∑ p:s.primes,(s.jD v p false + s.jD v p true) =
      ∑ p ∈ s.eligible v,Real.log (p:ℝ):=by
    rw [Finset.sum_coe_sort s.primes (fun p=>s.jD v p false + s.jD v p true),
      aE.eligible,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hp2:p ≠ 2:=by have hm:=s.Fy p hp; omega
    have hnot:=rS (s.iF p hp) hp2 (s.jc p hp) hv
    by_cases h1:s.factor p ∣ v <;> by_cases h2:star (s.factor p) ∣ v
    · exact False.elim (hnot ⟨h1,h2⟩)
    all_goals simp [aE.jD,dG,h1,h2]
  rw [← Finset.sum_div,heq]
  exact div_le_div_of_nonneg_right (s.JI hv0) (by norm_num)
theorem aE.Qm (s:aE) {v:GaussianInt}
    (hv:iG v) (hv0:v ≠ 0) {ε:ℝ} (hε:0 ≤ ε) :
    (gY s.primes).real {σ |
      Real.log (v.norm:ℝ) / 2 + ε ≤ ∑ p:s.primes,s.jD v p (σ p)}
    ≤ Real.exp (-ε ^ 2 / (2 * ∑ p:s.primes,
      (((‖Real.log (p:ℝ)‖₊ / 2) ^ 2:ℝ≥0):ℝ))):=by
  classical
  apply le_trans (measureReal_mono (s₂:={σ |
    ε + ∑ p:s.primes,(s.jD v p false + s.jD v p true) / 2 ≤
      ∑ p:s.primes,s.jD v p (σ p)}) ?_)
  · apply Oi (fun p:s.primes=>s.jD v p) (fun p=>Real.log (p:ℝ))
    · intro p b
      have hp:0 ≤ Real.log (p:ℝ):=Real.log_nonneg (by
        exact_mod_cast (s.iF p p.property).one_lt.le)
      unfold aE.jD
      split_ifs
      · exact ⟨hp,le_rfl⟩
      · exact ⟨le_rfl,hp⟩
    · exact hε
  · intro σ hσ
    have jE:=s.Ql hv hv0
    change Real.log (v.norm:ℝ) / 2 + ε ≤ _ at hσ
    change ε + _ ≤ _
    linarith
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9
namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal
abbrev Cube:ℕ → Type
  | 0=>Unit
  | n + 1=>Bool × Cube n
instance QX:(n:ℕ) → Fintype (Cube n)
  | 0=>inferInstanceAs (Fintype Unit)
  | n + 1=>@instFintypeProd Bool (Cube n) inferInstance (QX n)
instance Ni:(n:ℕ) → DecidableEq (Cube n)
  | 0=>inferInstanceAs (DecidableEq Unit)
  | n + 1=>@instDecidableEqProd Bool (Cube n) inferInstance (Ni n)
def d7:(n:ℕ) → Cube n → Cube n → ℕ
  | 0,_,_=>0
  | n + 1,(b,x),(c,y)=>(if b = c then 0 else 1) + d7 n x y
@[simp] theorem Vi (n:ℕ) (x:Cube n):d7 n x x = 0:=by
  induction n with
  | zero=>rfl
  | succ n ih=>obtain ⟨b,x⟩:=x; simp [d7,ih]
@[simp] theorem xW (n:ℕ) (x y:Cube n):d7 n x y = 0 ↔ x = y:=by
  induction n with
  | zero=>simp only [d7]
  | succ n ih =>
    obtain ⟨b,x⟩:=x
    obtain ⟨c,y⟩:=y
    by_cases h:b = c <;> simp [d7,h,ih,Prod.mk.injEq]
theorem Ih (n:ℕ) (x y:Cube n):d7 n x y = d7 n y x:=by
  induction n with
  | zero=>rfl
  | succ n ih =>
    obtain ⟨b,x⟩:=x
    obtain ⟨c,y⟩:=y
    simp [d7,eq_comm (a:=b) (b:=c),ih x y]
theorem xZ (n:ℕ) (x y z:Cube n) :
    d7 n x z ≤ d7 n x y + d7 n y z:=by
  induction n with
  | zero=>simp [d7]
  | succ n ih =>
    obtain ⟨b,x⟩:=x
    obtain ⟨c,y⟩:=y
    obtain ⟨d,z⟩:=z
    have h:=ih x y z
    cases b <;> cases c <;> cases d <;> simp [d7] <;> omega
noncomputable def cO {n:ℕ} (S:Cube n → Prop):ℕ:=by
  classical
  exact ∑ x,if S x then 1 else 0
noncomputable def j7 {n:ℕ} (S:Cube n → Prop):ℕ:=by
  classical
  exact ∑ x,∑ y,if S x ∧ ¬ S y ∧ d7 n x y = 1 then 1 else 0
noncomputable def lX {n:ℕ} (A B:Cube n → Prop):ℕ:=by
  classical
  exact ∑ x,if A x ∧ ¬ B x then 1 else 0
theorem Pd {n:ℕ} (S:Cube (n+1) → Prop) :
    cO S = cO (fun x=>S (false,x)) + cO (fun x=>S (true,x)):=by
  classical
  simp only [cO,Fintype.sum_prod_type,Fintype.sum_bool]
  ac_rfl
theorem K3 {n:ℕ} (S:Cube (n+1) → Prop) :
    j7 S = j7 (fun x=>S (false,x)) + j7 (fun x=>S (true,x)) +
      lX (fun x=>S (false,x)) (fun x=>S (true,x)) +
      lX (fun x=>S (true,x)) (fun x=>S (false,x)):=by
  classical
  simp only [j7,lX,Fintype.sum_prod_type,Fintype.sum_bool,d7,
    Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,zero_add,Nat.add_eq_left,
    xW,Finset.sum_add_distrib]
  simp only [and_assoc,and_left_comm,and_comm,ite_and,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
  omega
theorem yA {n:ℕ} (A B:Cube n → Prop):cO A ≤ cO B + lX A B:=by
  classical
  rw [cO,cO,lX,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha:A x <;> by_cases hb:B x <;> simp [ha,hb]
theorem QY (n:ℕ) (x:Cube n):(∑ y,if d7 n x y = 1 then 1 else 0) = n:=by
  classical
  induction n with
  | zero=>simp [d7]
  | succ n ih =>
    obtain ⟨b,x⟩:=x
    cases b <;> simp only [Fintype.sum_prod_type,Fintype.sum_bool,d7,
      Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,zero_add,Nat.add_eq_left,
      xW,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,ih]
    omega
theorem Ed {p:ℝ} (hp0:0 ≤ p) (hp2:p ≤ 1/2) :
    2 * p * Real.log 2 ≤ Real.binEntropy p:=by
  have hc:ConcaveOn ℝ (Set.Icc 0 1) Real.binEntropy:=Real.strictConcave_binEntropy.concaveOn
  have h:=hc.2 (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (2:ℝ)⁻¹ ∈ Set.Icc 0 1 by norm_num)
    (show 0 ≤ 1 - 2*p by linarith) (show 0 ≤ 2*p by positivity) (by ring)
  simpa only [smul_eq_mul,Real.binEntropy_zero,Real.binEntropy_two_inv,
    mul_zero,zero_add,show 2*p*(2:ℝ)⁻¹ = p by ring] using h
theorem tM {a b:ℝ} (ha:0 ≤ a) (hab:a ≤ b) :
    2 * a * Real.log 2 ≤ (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b:=by
  by_cases ha0:a = 0
  · simp [ha0]
  have hap:0 < a:=lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp:0 < b:=hap.trans_le hab
  have ht:0 < a+b:=by positivity
  have hp0:0 ≤ a/(a+b):=by positivity
  have hp2:a/(a+b) ≤ 1/2:=(div_le_iff₀ ht).mpr (by linarith)
  have h:=mul_le_mul_of_nonneg_left (Ed hp0 hp2) ht.le
  have heq:(a+b) * Real.binEntropy (a/(a+b)) =
      (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b:=by
    have hsub:1-a/(a+b) = b/(a+b):=by field_simp; ring
    rw [Real.binEntropy,hsub,Real.log_inv,Real.log_inv,
      Real.log_div hap.ne' ht.ne',Real.log_div hbp.ne' ht.ne']
    field_simp
    ring
  rw [heq] at h
  have heq':(a+b) * (2 * (a/(a+b)) * Real.log 2) = 2*a*Real.log 2:=by
    field_simp
  rwa [heq'] at h
theorem Pe {a b:ℝ} (ha:0 ≤ a) (hb:0 ≤ b) :
    2 * min a b * Real.log 2 ≤ (a+b)*Real.log (a+b) - a*Real.log a - b*Real.log b:=by
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab] using tM ha hab
  · have h:=tM hb hba
    rw [min_eq_right hba]
    convert h using 1
    rw [add_comm b a]
    ring
theorem BL (n:ℕ) (S:Cube n → Prop) :
    (cO S:ℝ) * ((n:ℝ) * Real.log 2 - Real.log (cO S)) ≤
      (j7 S:ℝ) * Real.log 2:=by
  classical
  induction n with
  | zero =>
    by_cases hs:S () <;> simp [cO,j7,d7,hs]
  | succ n ih =>
    have h0:=ih (fun x=>S (false,x))
    have h1:=ih (fun x=>S (true,x))
    have hac:=yA (fun x=>S (false,x)) (fun x=>S (true,x))
    have hbc:=yA (fun x=>S (true,x)) (fun x=>S (false,x))
    have Zj:(cO (fun x=>S (false,x)):ℝ) ≤
        cO (fun x=>S (true,x)) + lX (fun x=>S (false,x)) (fun x=>S (true,x)):=by
      exact_mod_cast hac
    have hbc':(cO (fun x=>S (true,x)):ℝ) ≤
        cO (fun x=>S (false,x)) + lX (fun x=>S (true,x)) (fun x=>S (false,x)):=by
      exact_mod_cast hbc
    have he:=Pe (a:=(cO (fun x=>S (false,x)):ℝ))
      (b:=(cO (fun x=>S (true,x)):ℝ)) (by positivity) (by positivity)
    have hl:0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
    rw [Pd,K3]
    push_cast
    rcases le_total (cO (fun x=>S (false,x)):ℝ) (cO (fun x=>S (true,x)):ℝ) with hab | hba
    · rw [min_eq_left hab] at he
      have hn:(0:ℝ) ≤ lX (fun x=>S (false,x)) (fun x=>S (true,x)):=by positivity
      nlinarith
    · rw [min_eq_right hba] at he
      have hn:(0:ℝ) ≤ lX (fun x=>S (true,x)) (fun x=>S (false,x)):=by positivity
      nlinarith
def lY {n:ℕ} (S:Cube n → Prop) (y:Cube n):Prop :=
  S y ∨ ∃ x,S x ∧ d7 n x y = 1
def e8 {n:ℕ} (S:Cube n → Prop):ℕ → Cube n → Prop
  | 0=>S
  | h+1=>lY (e8 S h)
theorem Ph {n:ℕ} {S T:Cube n → Prop} (h:∀ x,S x → T x) :
    cO S ≤ cO T:=by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hs:S x
  · simp [hs,h x hs]
  · simp [hs]
theorem O2 (n:ℕ):Fintype.card (Cube n) = 2^n:=by
  induction n with
  | zero=>rfl
  | succ n ih =>
    change Fintype.card (Bool × Cube n) = _
    rw [Fintype.card_prod,Fintype.card_bool,ih,pow_succ]
    omega
theorem Ww (n:ℕ) (S:Cube n → Prop):cO S ≤ 2^n:=by
  classical
  calc
    cO S ≤ ∑ _:Cube n,1:=by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> omega
    _ = 2^n:=by simp [O2]
theorem yW {n:ℕ} (S:Cube n → Prop) :
    j7 S + n * cO S ≤ n * cO (lY S):=by
  classical
  have hdegree (y:Cube n) :
      (∑ x,if S x ∧ ¬ S y ∧ d7 n x y = 1 then 1 else 0) ≤
        n * (if ¬S y ∧ (∃ x,S x ∧ d7 n x y = 1) then 1 else 0):=by
    by_cases hy:¬S y ∧ (∃ x,S x ∧ d7 n x y = 1)
    · rw [dO hy,mul_one]
      calc
        _ ≤ ∑ x,if d7 n y x = 1 then 1 else 0:=by
          apply Finset.sum_le_sum
          intro x _
          by_cases h:S x ∧ ¬ S y ∧ d7 n x y = 1
          · simp [h,Ih n y x]
          · simp [h]
        _ = n:=QY n y
    · simp only [hy,↓reduceIte,mul_zero,Nat.le_zero]
      apply Finset.sum_eq_zero
      intro x _
      have hnot:¬(S x ∧ ¬S y ∧ d7 n x y = 1):=by
        rintro ⟨hs,hns,hd⟩
        exact hy ⟨hns,x,hs,hd⟩
      simp [hnot]
  have hb:=Finset.sum_le_sum (s:=Finset.univ) (fun y _=>hdegree y)
  rw [← Finset.mul_sum] at hb
  have heq:cO (lY S) = cO S +
      ∑ y,if ¬S y ∧ (∃ x,S x ∧ d7 n x y = 1) then 1 else 0:=by
    rw [cO,cO,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hs:S y <;> simp [lY,hs]
  unfold j7
  rw [Finset.sum_comm,heq,Nat.mul_add]
  omega
theorem qu {n h:ℕ} {S:Cube n → Prop} {x:Cube n}
    (hx:e8 S h x):∃ y,S y ∧ d7 n y x ≤ h:=by
  induction h generalizing x with
  | zero=>exact ⟨x,hx,by simp⟩
  | succ h ih =>
    rcases hx with hx | ⟨z,hz,hzx⟩
    · obtain ⟨y,hy,hyx⟩:=ih hx
      exact ⟨y,hy,by omega⟩
    · obtain ⟨y,hy,hyz⟩:=ih hz
      exact ⟨y,hy,by have ht:=xZ n y z x; omega⟩
theorem BT {n h:ℕ} {S T:Cube n → Prop}
    (hsep:∀ x,S x → ∀ y,T y → 2*h < d7 n x y) :
    ∀ x,¬(e8 S h x ∧ e8 T h x):=by
  rintro x ⟨hs,ht⟩
  obtain ⟨y,hy,hyx⟩:=qu hs
  obtain ⟨z,hz,hzx⟩:=qu ht
  have h:=hsep y hy z hz
  have htri:=xZ n y x z
  rw [Ih n x z] at htri
  omega
theorem Nj {n:ℕ} {ι:Type c9} [Fintype ι] (S:ι → Cube n → Prop)
    (hd:∀ i j,i ≠ j → ∀ x,¬(S i x ∧ S j x)) :
    ∑ i,cO (S i) ≤ 2^n:=by
  classical
  unfold cO
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _:Cube n,1:=by
      apply Finset.sum_le_sum
      intro x _
      by_cases he:∃ i,S i x
      · obtain ⟨i,hi⟩:=he
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hji
          have hnot:¬S j x:=fun hj=>hd j i hji x ⟨hj,hi⟩
          simp [hnot]
        · simp
      · have hh:∀ i,¬S i x:=by simpa only [not_exists] using he
        simp [hh]
    _ = 2^n:=by simp [O2]
theorem QZ {n:ℕ} (hn:0 < n) (S:Cube n → Prop) {a E:ℝ}
    (hE:0 < E) (Nk:Real.log E ≤ (n:ℝ) * Real.log 2 - a)
    (hsize:(cO S:ℝ) ≤ E) :
    (1 + a / ((n:ℝ) * Real.log 2)) * cO S ≤ cO (lY S):=by
  by_cases hz:cO S = 0
  · simp [hz]
  have hpos:(0:ℝ) < cO S:=by exact_mod_cast Nat.pos_of_ne_zero hz
  have hnpos:(0:ℝ) < n:=by exact_mod_cast hn
  have Ru:0 < Real.log 2:=Real.log_pos (by norm_num)
  have hden:0 < (n:ℝ) * Real.log 2:=mul_pos hnpos Ru
  have hl:=((Real.log_le_log_iff hpos hE).mpr hsize).trans Nk
  have hi:=BL n S
  have hb:(j7 S:ℝ) + n * cO S ≤ n * cO (lY S):=by
    exact_mod_cast yW S
  apply (mul_le_mul_iff_left₀ hden).mp
  field_simp at ⊢
  nlinarith [mul_le_mul_of_nonneg_left hl hpos.le,
    mul_le_mul_of_nonneg_right hb Ru.le]
theorem LO {n:ℕ} (S:Cube n → Prop) {δ E:ℝ} (hδ:0 ≤ δ)
    (WB:∀ T:Cube n → Prop,(cO T:ℝ) ≤ E →
      (1+δ)*cO T ≤ cO (lY T)) (h:ℕ) :
    min E ((1+δ)^h * cO S) ≤ cO (e8 S h):=by
  induction h with
  | zero=>simpa only [pow_zero,one_mul,e8] using
      (min_le_right E (cO S:ℝ))
  | succ h ih =>
    have hmono:(cO (e8 S h):ℝ) ≤ cO (e8 S (h+1)):=by
      exact_mod_cast Ph (S:=e8 S h) (T:=lY (e8 S h))
        (fun _ hx=>Or.inl hx)
    by_cases cQ:E ≤ (cO (e8 S h):ℝ)
    · exact (min_le_left _ _).trans (cQ.trans hmono)
    · have jd:(cO (e8 S h):ℝ) ≤ E:=le_of_not_ge cQ
      have hpow:(1+δ)^h * cO S ≤ E:=by
        by_contra hnot
        rw [min_eq_left (le_of_not_ge hnot)] at ih
        exact cQ ih
      rw [min_eq_right hpow] at ih
      have hmul:=mul_le_mul_of_nonneg_left ih (by linarith:0 ≤ 1+δ)
      have hg:=WB (e8 S h) jd
      apply (min_le_right _ _).trans
      simpa only [pow_succ,mul_assoc,mul_left_comm,e8] using hmul.trans hg
theorem Fz {n h:ℕ} (hn:0 < n) {ι:Type c9} [Fintype ι]
    (S:ι → Cube n → Prop) {a E A:ℝ} (ha:0 ≤ a) (hE:0 < E)
    (Nk:Real.log E ≤ (n:ℝ) * Real.log 2 - a)
    (RG:∀ i,A * cO (S i) ≤ E)
    (uO:A ≤ (1 + a / ((n:ℝ)*Real.log 2))^h)
    (hsep:∀ i j,i ≠ j → ∀ x,S i x → ∀ y,S j y → 2*h < d7 n x y) :
    A * (∑ i,(cO (S i):ℝ)) ≤ (2:ℝ)^n:=by
  have hδ:0 ≤ a / ((n:ℝ)*Real.log 2):=by
    apply div_nonneg ha
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have cQ (i:ι):A * cO (S i) ≤ cO (e8 (S i) h):=by
    apply le_trans (le_min (RG i) (mul_le_mul_of_nonneg_right uO (Nat.cast_nonneg _)))
    exact LO (S i) hδ (fun T ht=>QZ hn T hE Nk ht) h
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun i _=>cQ i)).trans
  have hd:∀ i j,i ≠ j → ∀ x,¬(e8 (S i) h x ∧ e8 (S j) h x):=by
    intro i j hij
    exact BT (hsep i j hij)
  exact_mod_cast Nj (fun i=>e8 (S i) h) hd
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9
namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal
def oF:(n:ℕ) → Cube n ≃ (Fin n → Bool)
  | 0=>{
      toFun:=fun _ i=>Fin.elim0 i
      invFun:=fun _=>()
      left_inv:=fun x=>by cases x; rfl
      right_inv:=fun f=>by funext i; exact Fin.elim0 i }
  | n+1=>(Equiv.prodCongr (Equiv.refl Bool) (oF n)).trans (Fin.consEquiv (fun _=>Bool))
noncomputable def jC (ι:Type c9) [Fintype ι]:Cube (Fintype.card ι) ≃ (ι → Bool) :=
  (oF (Fintype.card ι)).trans
    (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl Bool))
noncomputable def kS {ι:Type c9} [Fintype ι] (σ τ:ι → Bool):ℕ:=by
  classical
  exact ∑ i,if σ i = τ i then 0 else 1
theorem Oj (n:ℕ) (x y:Cube n) :
    kS (oF n x) (oF n y) = d7 n x y:=by
  classical
  induction n with
  | zero=>simp [kS,d7]
  | succ n ih =>
    obtain ⟨b,x⟩:=x
    obtain ⟨c,y⟩:=y
    simp only [kS,Fin.sum_univ_succ,oF,Equiv.trans_apply,
      Equiv.prodCongr_apply,Fin.consEquiv_apply,Fin.cons_zero,
      Fin.cons_succ,d7]
    congr 1
    exact ih x y
theorem JK (ι:Type c9) [Fintype ι] (x y:Cube (Fintype.card ι)) :
    kS (jC ι x) (jC ι y) = d7 (Fintype.card ι) x y:=by
  classical
  rw [← Oj]
  unfold kS jC
  simp only [Equiv.trans_apply,Equiv.arrowCongr_apply,Equiv.symm_symm]
  exact (Fintype.equivFin ι).sum_comp (fun i=>if oF (Fintype.card ι) x i =
    oF (Fintype.card ι) y i then (0:ℕ) else 1)
theorem wQ {ι:Type c9} [Fintype ι] (σ:ι → Bool) :
    (gY ι).real {σ} = ((2:ℝ)^Fintype.card ι)⁻¹:=by
  simp [measureReal_def,gY,Measure.pi_singleton,nL,
    PMF.uniformOfFintype_apply]
open scoped Classical in
theorem rV {ι:Type c9} [Fintype ι] (S:Set (ι → Bool)) :
    (gY ι).real S = (∑ σ,if σ ∈ S then (1:ℝ) else 0) /
      (2:ℝ)^Fintype.card ι:=by
  classical
  have he:S = (↑(Finset.univ.filter (· ∈ S)):Set (ι → Bool)):=by ext; simp
  conv_lhs=>rw [he,← sum_measureReal_singleton]
  rw [Finset.sum_filter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ:σ ∈ S <;> simp [hσ,wQ]
theorem q7 {ι:Type c9} [Fintype ι] (S:(ι → Bool) → Prop) :
    (gY ι).real {σ | S σ} =
      (cO (fun x=>S (jC ι x)):ℝ) / (2:ℝ)^Fintype.card ι:=by
  classical
  rw [rV]
  congr 1
  simp only [Set.mem_ofPred_eq]
  rw [← (jC ι).sum_comp (fun σ=>if S σ then (1:ℝ) else 0)]
  simp only [cO,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
noncomputable def aE.fG (s:aE) (σ:s.primes → Bool) (p:ℕ):Bool:=by
  classical
  exact if hp:p ∈ s.primes then σ ⟨p,hp⟩ else false
@[simp] theorem aE.Nl (s:aE) (σ:s.primes → Bool)
    (p:ℕ) (hp:p ∈ s.primes):s.fG σ p = σ ⟨p,hp⟩:=by
  simp [aE.fG,hp]
noncomputable def aE.kA (s:aE) (σ:s.primes → Bool):GaussianInt :=
  ∏ p ∈ s.primes,dG (s.factor p) (s.fG σ p)
theorem aE.Dm (s:aE) (σ:s.primes → Bool)
    {v w:GaussianInt} (hv:iG v) (hv0:v ≠ 0) (hw:w ≠ 0)
    (Nh:determinant v w = 0) (hdiv:s.kA σ ∣ w)
    {B:ℝ} (hbound:(w.norm:ℝ) ≤ B) :
    Real.log (v.norm:ℝ) / 2 + (∑ p:s.primes,Real.log (p:ℝ)) - Real.log B / 2 ≤
      ∑ p:s.primes,s.jD v p (σ p):=by
  classical
  let t:=s.primes.filter (fun p=>¬dG (s.factor p) (s.fG σ p) ∣ v)
  have hp (p:ℕ) (hp:p ∈ t):0 < (p:ℝ):=by
    exact_mod_cast (s.iF p (Finset.mem_filter.mp hp).1).pos
  have hprod:0 < ∏ p ∈ t,(p:ℝ):=Finset.prod_pos hp
  have Ue:0 < (v.norm:ℝ):=by exact_mod_cast (GaussianInt.norm_pos.mpr hv0)
  have hlo:=s.BK s.primes (fun _ h=>h) (s.fG σ) hv hw Nh hdiv
  have kT:(v.norm:ℝ) * (∏ p ∈ t,(p:ℝ))^2 ≤ B:=by
    apply le_trans ?_ hbound
    have hc:((v.norm * (∏ p ∈ t,(p:ℤ))^2:ℤ):ℝ) ≤ (w.norm:ℝ):=by exact_mod_cast hlo
    push_cast at hc
    exact hc
  have hlog:=Real.log_le_log (mul_pos Ue (sq_pos_of_pos hprod)) kT
  rw [Real.log_mul Ue.ne' (sq_pos_of_pos hprod).ne',Real.log_pow,
    Real.log_prod (fun p hp'=>(hp p hp').ne')] at hlog
  have hsum:(∑ p ∈ t,Real.log (p:ℝ)) =
      (∑ p:s.primes,Real.log (p:ℝ)) - ∑ p:s.primes,s.jD v p (σ p):=by
    calc
      _ = ∑ p ∈ s.primes,(Real.log (p:ℝ) - s.jD v p (s.fG σ p)):=by
        unfold t
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp'
        unfold aE.jD
        split_ifs <;> simp_all
      _ = _:=by
        rw [← Finset.sum_coe_sort s.primes
          (fun p=>Real.log (p:ℝ) - s.jD v p (s.fG σ p))]
        simp [aE.fG,Finset.sum_sub_distrib]
  rw [hsum] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]
def aE.O4 (s:aE) (Q:Set GaussianInt) (v:GaussianInt)
    (σ:s.primes → Bool):Prop :=
  ∃ w ∈ Q,w ≠ 0 ∧ determinant v w = 0 ∧ s.kA σ ∣ w
theorem aE.Nm (s:aE) {Q:Set GaussianInt}
    {v:GaussianInt} (hv:iG v) (hv0:v ≠ 0) {B ε:ℝ}
    (hQ:∀ w ∈ Q,(w.norm:ℝ) ≤ B) (hε:0 ≤ ε)
    (zU:ε ≤ (∑ p:s.primes,Real.log (p:ℝ)) - Real.log B / 2) :
    (gY s.primes).real {σ | s.O4 Q v σ} ≤
      Real.exp (-ε^2 / (2 * ∑ p:s.primes,
        (((‖Real.log (p:ℝ)‖₊ / 2)^2:ℝ≥0):ℝ))):=by
  apply le_trans (measureReal_mono (s₂:={σ |
    Real.log (v.norm:ℝ) / 2 + ε ≤ ∑ p:s.primes,s.jD v p (σ p)}) ?_)
  · exact s.Qm hv hv0 hε
  · rintro σ ⟨w,Yz,hw,Nh,hd⟩
    have hl:=s.Dm σ hv hv0 hw Nh hd (hQ w Yz)
    change Real.log (v.norm:ℝ) / 2 + ε ≤ _
    linarith
open scoped Classical in
noncomputable def aE.jT (s:aE) (σ τ:s.primes → Bool):GaussianInt :=
  ∏ p ∈ s.primes.filter (fun p=>s.fG σ p = s.fG τ p),
    dG (s.factor p) (s.fG σ p)
theorem aE.qv (s:aE) (σ τ:s.primes → Bool) :
    s.jT σ τ ∣ s.kA σ:=by
  classical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
theorem aE.JL (s:aE) (σ τ:s.primes → Bool) :
    s.jT σ τ = s.jT τ σ:=by
  classical
  unfold aE.jT
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter,eq_comm]
  · intro p hp
    rw [(Finset.mem_filter.mp hp).2]
theorem aE.BU (s:aE) (σ τ:s.primes → Bool) :
    s.jT σ τ ∣ s.kA τ:=by
  rw [s.JL]
  exact s.qv τ σ
open scoped Classical in
theorem aE.LQ (s:aE) (σ τ:s.primes → Bool) :
    kS σ τ = (s.primes.filter (fun p=>s.fG σ p ≠ s.fG τ p)).card:=by
  classical
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,← Finset.sum_coe_sort s.primes
    (fun p=>if s.fG σ p ≠ s.fG τ p then 1 else 0)]
  unfold kS
  apply Finset.sum_congr rfl
  intro p _
  simp [aE.fG]
theorem aE.Ee (s:aE) (σ τ:s.primes → Bool)
    {U:ℝ} (hpU:∀ p ∈ s.primes,(p:ℝ) ≤ U) :
    (s.period:ℝ) ≤ ((s.jT σ τ).norm:ℝ) * U^(kS σ τ):=by
  classical
  let c:=s.primes.filter (fun p=>s.fG σ p = s.fG τ p)
  let d:=s.primes.filter (fun p=>s.fG σ p ≠ s.fG τ p)
  have hc:((s.jT σ τ).norm:ℝ) = ∏ p ∈ c,(p:ℝ):=by
    unfold aE.jT
    rw [z5,Int.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [iW,s.jc p (Finset.mem_filter.mp hp).1]
    exact_mod_cast (rfl:(p:ℝ) = p)
  have hd:(∏ p ∈ d,(p:ℝ)) ≤ U^d.card:=by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun p _=>Nat.cast_nonneg p)
      (fun p hp=>hpU p (Finset.mem_filter.mp hp).1)
  have hp:(s.period:ℝ) = (∏ p ∈ c,(p:ℝ)) * (∏ p ∈ d,(p:ℝ)):=by
    unfold aE.period
    push_cast
    exact (Finset.prod_filter_mul_prod_filter_not s.primes
      (fun p=>s.fG σ p = s.fG τ p) (fun p=>(p:ℝ))).symm
  rw [hp,hc,s.LQ]
  exact mul_le_mul_of_nonneg_left hd (Finset.prod_nonneg (fun p _=>Nat.cast_nonneg p))
theorem aE.z8 (s:aE) (σ τ:s.primes → Bool)
    {w w':GaussianInt} (hw:s.kA σ ∣ w) (hw':s.kA τ ∣ w')
    {U B:ℝ} (hU:0 < U) (hpU:∀ p ∈ s.primes,(p:ℝ) ≤ U)
    (hdet:(|determinant w w'|:ℝ) ≤ B)
    (jd:B * U^(kS σ τ) < (s.period:ℝ)):determinant w w' = 0:=by
  have hbound:=lt_of_lt_of_le jd (s.Ee σ τ hpU)
  have hlt:B < ((s.jT σ τ).norm:ℝ) :=
    (mul_lt_mul_iff_left₀ (pow_pos hU _)).mp (by simpa only [mul_comm] using hbound)
  apply oC
    ((s.qv σ τ).trans hw) ((s.BU σ τ).trans hw')
  exact_mod_cast hdet.trans_lt hlt
theorem qw {u v w:GaussianInt} (hv:v ≠ 0)
    (huv:determinant u v = 0) (hvw:determinant v w = 0) :
    determinant u w = 0:=by
  have Vr:v.re ≠ 0 ∨ v.im ≠ 0:=by
    contrapose! hv
    ext <;> simp [hv.1,hv.2]
  unfold determinant at *
  rcases Vr with hr | hi
  · apply (mul_eq_zero.mp (show v.re * (u.re * w.im - u.im * w.re) = 0 by
      nlinarith [congrArg (fun x:ℤ=>x * w.re) huv,
        congrArg (fun x:ℤ=>u.re * x) hvw])).resolve_left hr
  · apply (mul_eq_zero.mp (show v.im * (u.re * w.im - u.im * w.re) = 0 by
      nlinarith [congrArg (fun x:ℤ=>x * w.im) huv,
        congrArg (fun x:ℤ=>u.im * x) hvw])).resolve_left hi
@[simp] theorem LV (v:GaussianInt):determinant v v = 0:=by
  unfold determinant
  ring
theorem LW (u v:GaussianInt):determinant u v = -determinant v u:=by
  unfold determinant
  ring
def k6 (v:GaussianInt):Set GaussianInt:={w | determinant v w = 0}
theorem Eh {v w:GaussianInt} (hv:v ≠ 0) (hw:w ≠ 0)
    (hvw:determinant v w = 0):k6 v = k6 w:=by
  ext u
  constructor
  · intro hu
    exact qw hv (by rw [LW,hvw,neg_zero]) hu
  · exact qw hw hvw
def aE.kG (s:aE) (Q:Set GaussianInt) (σ:s.primes → Bool):Prop :=
  ∃ w ∈ Q,w ≠ 0 ∧ s.kA σ ∣ w
noncomputable def aE.nO (s:aE) (Q:Set GaussianInt)
    (σ:{σ:s.primes → Bool // s.kG Q σ}):GaussianInt:=σ.property.choose
theorem aE.og (s:aE) (Q:Set GaussianInt)
    (σ:{σ:s.primes → Bool // s.kG Q σ}) :
    s.nO Q σ ∈ Q ∧ s.nO Q σ ≠ 0 ∧ s.kA σ.val ∣ s.nO Q σ :=
  σ.property.choose_spec
def aE.lB (s:aE) (Q:Set GaussianInt):Set (Set GaussianInt) :=
  Set.range (fun σ:{σ:s.primes → Bool // s.kG Q σ}=>k6 (s.nO Q σ))
instance aE.Uh (s:aE) (Q:Set GaussianInt) :
    Finite (s.lB Q):=by
  unfold aE.lB
  infer_instance
theorem aE.K4 (s:aE) (Q:Set GaussianInt)
    (L:s.lB Q):∃ v:GaussianInt,iG v ∧ v ≠ 0 ∧ k6 v = L.val:=by
  obtain ⟨σ,hσ⟩:=L.property
  have hw:=s.og Q σ
  obtain ⟨v,hv,hv0,a,Y9,ha⟩:=wP hw.2.1
  refine ⟨v,hv,hv0,?_⟩
  rw [← hσ]
  apply Eh hv0 hw.2.1
  rw [ha]
  unfold determinant
  simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast]
  ring
def aE.vO (s:aE) (Q:Set GaussianInt) (L:s.lB Q)
    (σ:s.primes → Bool):Prop :=
  ∃ hσ:s.kG Q σ,k6 (s.nO Q ⟨σ,hσ⟩) = L.val
theorem aE.K5 (s:aE) (Q:Set GaussianInt) (σ:s.primes → Bool) :
    s.kG Q σ ↔ ∃ L:s.lB Q,s.vO Q L σ:=by
  constructor
  · intro hσ
    exact ⟨⟨k6 (s.nO Q ⟨σ,hσ⟩),⟨⟨σ,hσ⟩,rfl⟩⟩,hσ,rfl⟩
  · rintro ⟨L,hσ,_⟩
    exact hσ
theorem aE.Dp (s:aE) (Q:Set GaussianInt)
    (L:s.lB Q) {v:GaussianInt} (Vt:k6 v = L.val) :
    {σ | s.vO Q L σ} ⊆ {σ | s.O4 Q v σ}:=by
  rintro σ ⟨hσ,hL⟩
  have hw:=s.og Q ⟨σ,hσ⟩
  refine ⟨_,hw.1,hw.2.1,?_,hw.2.2⟩
  change s.nO Q ⟨σ,hσ⟩ ∈ k6 v
  rw [Vt,← hL]
  exact LV _
theorem aE.Ej (s:aE) (Q:Set GaussianInt)
    {U B:ℝ} (hU:1 ≤ U) (hpU:∀ p ∈ s.primes,(p:ℝ) ≤ U)
    (hdet:∀ w ∈ Q,∀ w' ∈ Q,(|determinant w w'|:ℝ) ≤ B)
    {h:ℕ} (jd:B * U^(2*h) < (s.period:ℝ)) (hB:0 ≤ B) :
    ∀ L L':s.lB Q,L ≠ L' → ∀ σ,s.vO Q L σ →
      ∀ τ,s.vO Q L' τ → 2*h < kS σ τ:=by
  intro L L' SM σ ⟨hσ,YA⟩ τ ⟨hτ,YB⟩
  by_contra hn
  have hd:kS σ τ ≤ 2*h:=le_of_not_gt hn
  have hw:=s.og Q ⟨σ,hσ⟩
  have hw':=s.og Q ⟨τ,hτ⟩
  have hsm:B * U^(kS σ τ) < (s.period:ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU hd) hB).trans_lt jd
  have hcol:=s.z8 σ τ hw.2.2 hw'.2.2 (by linarith) hpU
    (hdet _ hw.1 _ hw'.1) hsm
  apply SM
  apply Subtype.ext
  rw [← YA,← YB]
  exact Eh hw.2.1 hw'.2.1 hcol
theorem Dq {n:ℕ} {ι:Type c9} [Fintype ι]
    (S:ι → Cube n → Prop):cO (fun x=>∃ i,S i x) ≤ ∑ i,cO (S i):=by
  classical
  unfold cO
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx:∃ i,S i x
  · obtain ⟨i,hi⟩:=hx
    rw [dO ⟨i,hi⟩]
    have h:(if S i x then 1 else 0) ≤ ∑ j:ι,if S j x then 1 else 0 :=
      Finset.single_le_sum (f:=fun j=>if S j x then (1:ℕ) else 0)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    simpa only [dO hi] using h
  · simp only [gR hx]
    exact Nat.zero_le _
theorem aE.IG (s:aE) (Q:Set GaussianInt)
    (hr:0 < s.primes.card) {U B N ε a E A:ℝ} {h:ℕ}
    (hU:1 ≤ U) (hpU:∀ p ∈ s.primes,(p:ℝ) ≤ U)
    (hB:0 ≤ B) (hdet:∀ w ∈ Q,∀ w' ∈ Q,(|determinant w w'|:ℝ) ≤ B)
    (jd:B * U^(2*h) < (s.period:ℝ))
    (hQ:∀ w ∈ Q,(w.norm:ℝ) ≤ N) (hε:0 ≤ ε)
    (zU:ε ≤ (∑ p:s.primes,Real.log (p:ℝ)) - Real.log N / 2)
    (ha:0 ≤ a) (hE:0 < E) (hA:0 < A)
    (Nk:Real.log E ≤ (s.primes.card:ℝ) * Real.log 2 - a)
    (RG:A * Real.exp (-ε^2 / (2 * ∑ p:s.primes,
      (((‖Real.log (p:ℝ)‖₊ / 2)^2:ℝ≥0):ℝ))) * (2:ℝ)^s.primes.card ≤ E)
    (uO:A ≤ (1 + a / ((s.primes.card:ℝ)*Real.log 2))^h) :
    (gY s.primes).real {σ | s.kG Q σ} ≤ A⁻¹:=by
  classical
  let:Fintype (s.lB Q):=Fintype.ofFinite _
  let S:s.lB Q → Cube (Fintype.card s.primes) → Prop :=
    fun L x=>s.vO Q L (jC s.primes x)
  have hcard:Fintype.card s.primes = s.primes.card:=Fintype.card_coe _
  have hpow:0 < (2:ℝ)^Fintype.card s.primes:=pow_pos (by norm_num) _
  have Vv (L:s.lB Q):A * cO (S L) ≤ E:=by
    obtain ⟨v,hv,hv0,Vt⟩:=s.K4 Q L
    have hm:=(measureReal_mono (s.Dp Q L Vt)).trans
      (s.Nm hv hv0 hQ hε zU)
    rw [q7] at hm
    have hc:(cO (S L):ℝ) ≤ Real.exp (-ε^2 / (2 * ∑ p:s.primes,
        (((‖Real.log (p:ℝ)‖₊ / 2)^2:ℝ≥0):ℝ))) * (2:ℝ)^Fintype.card s.primes :=
      (div_le_iff₀ hpow).mp hm
    have hh:=mul_le_mul_of_nonneg_left hc hA.le
    exact hh.trans (by simpa only [hcard,mul_assoc] using RG)
  have hsep:∀ L L':s.lB Q,L ≠ L' → ∀ x,S L x → ∀ y,S L' y →
      2*h < d7 (Fintype.card s.primes) x y:=by
    intro L L' SM x hx y hy
    have hh:=s.Ej Q hU hpU hdet jd hB L L' SM
      (jC s.primes x) hx (jC s.primes y) hy
    simpa only [JK] using hh
  have WC:=Fz (n:=Fintype.card s.primes) (h:=h)
    (by simpa only [hcard] using hr) S ha hE (by simpa only [hcard] using Nk)
    Vv (by simpa only [hcard] using uO) hsep
  have hunion:(cO (fun x=>s.kG Q (jC s.primes x)):ℝ) ≤
      ∑ L,(cO (S L):ℝ):=by
    have he:(fun x=>s.kG Q (jC s.primes x)) = (fun x=>∃ L,S L x):=by
      funext x
      exact propext (s.K5 Q _)
    rw [he]
    exact_mod_cast Dq S
  rw [q7,div_le_iff₀ hpow]
  have hh:=(mul_le_mul_of_nonneg_left hunion hA.le).trans WC
  calc
    _ ≤ (2:ℝ)^Fintype.card s.primes / A:=(le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh)
    _ = _:=by rw [div_eq_mul_inv,mul_comm]
theorem aE.BW (s:aE) (Q:Set GaussianInt)
    (hr:0 < s.primes.card) {U B N ε a b:ℝ} {h:ℕ}
    (hU:1 ≤ U) (hpU:∀ p ∈ s.primes,(p:ℝ) ≤ U)
    (hB:0 ≤ B) (hdet:∀ w ∈ Q,∀ w' ∈ Q,(|determinant w w'|:ℝ) ≤ B)
    (jd:B * U^(2*h) < (s.period:ℝ))
    (hQ:∀ w ∈ Q,(w.norm:ℝ) ≤ N) (hε:0 ≤ ε)
    (zU:ε ≤ (∑ p:s.primes,Real.log (p:ℝ)) - Real.log N / 2)
    (ha:0 ≤ a) (hb:b ≤ a)
    (htail:2*a ≤ ε^2 / (2 * ∑ p:s.primes,
      (((‖Real.log (p:ℝ)‖₊ / 2)^2:ℝ≥0):ℝ)))
    (hgrowth:b ≤ (h:ℝ) * Real.log (1 + a / ((s.primes.card:ℝ)*Real.log 2))) :
    (gY s.primes).real {σ | s.kG Q σ} ≤ Real.exp (-b):=by
  have htwo:0 < Real.log 2:=Real.log_pos (by norm_num)
  have hr':0 < (s.primes.card:ℝ):=by exact_mod_cast hr
  have hbase:0 < 1 + a / ((s.primes.card:ℝ)*Real.log 2):=by
    have:=div_nonneg ha (mul_pos hr' htwo).le
    linarith
  have WE:Real.exp b ≤ (1 + a / ((s.primes.card:ℝ)*Real.log 2))^h:=by
    rw [← Real.exp_log (pow_pos hbase h)]
    apply Real.exp_le_exp.mpr
    simpa only [Real.log_pow] using hgrowth
  have hh:=s.IG Q hr hU hpU hB hdet jd hQ hε zU ha
    (E:=(2:ℝ)^s.primes.card * Real.exp (-a))
    (A:=Real.exp b) (h:=h) (mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _))
    (Real.exp_pos _) (by
      rw [Real.log_mul (pow_pos (by norm_num:(0:ℝ) < 2) _).ne' (Real.exp_pos _).ne',
        Real.log_pow,Real.log_exp]
      linarith) (by
      rw [← Real.exp_add]
      have he:b + -ε^2 / (2 * ∑ p:s.primes,
          (((‖Real.log (p:ℝ)‖₊ / 2)^2:ℝ≥0):ℝ)) ≤ -a:=by
        rw [neg_div]
        linarith
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (by norm_num) _)).trans_eq (mul_comm _ _)) WE
  simpa only [Real.exp_neg] using hh
def gC (e:ℂ) (R W:ℝ):Set GaussianInt :=
  {z | |(star e * (z:ℂ)).re| ≤ R ∧ |(star e * (z:ℂ)).im| ≤ W}
theorem FH {e:ℂ} (he:‖e‖ = 1) {R W:ℝ}
    (hW:0 ≤ W) (q8:W ≤ R) {z:GaussianInt} (hz:z ∈ gC e R W) :
    (z.norm:ℝ) ≤ 2 * R^2:=by
  have hnorm:‖star e * (z:ℂ)‖ = ‖(z:ℂ)‖:=by
    rw [norm_mul,norm_star,he,one_mul]
  rw [tL,← hnorm,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  have hx:(star e * (z:ℂ)).re ^ 2 ≤ R^2:=by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((star e * (z:ℂ)).re))
      (hW.trans q8)).mpr hz.1
  have hy:(star e * (z:ℂ)).im ^ 2 ≤ W^2:=by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg ((star e * (z:ℂ)).im)) hW).mpr hz.2
  have hww:=(sq_le_sq₀ hW (hW.trans q8)).mpr q8
  nlinarith
theorem IL (e:ℂ) (he:‖e‖ = 1) (z w:GaussianInt) :
    (determinant z w:ℝ) =
      (star e * (z:ℂ)).re * (star e * (w:ℂ)).im -
      (star e * (z:ℂ)).im * (star e * (w:ℂ)).re:=by
  have hsq:e.re^2 + e.im^2 = 1:=by
    have hh:=Complex.normSq_eq_norm_sq e
    rw [he] at hh
    simpa [Complex.normSq_apply,pow_two] using hh
  simp only [Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    ← GaussianInt.intCast_re,← GaussianInt.intCast_im,determinant,Int.cast_sub,Int.cast_mul]
  nlinarith [congrArg (fun x:ℝ=>x * ((z.re:ℝ) * w.im - z.im * w.re)) hsq]
theorem vP {e:ℂ} (he:‖e‖ = 1) {R W:ℝ}
    (hR:0 ≤ R) (hW:0 ≤ W) {z w:GaussianInt}
    (hz:z ∈ gC e R W) (hw:w ∈ gC e R W) :
    (|determinant z w|:ℝ) ≤ 2*R*W:=by
  rw [IL e he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul]
  have h1:=mul_le_mul hz.1 hw.2 (abs_nonneg _) hR
  have h2:=mul_le_mul hz.2 hw.1 (abs_nonneg _) hW
  nlinarith
theorem Ek {r:ℕ} {d:ℝ} (hd:0 < d) (hd1:d ≤ 1/4)
    (cQ:1000 ≤ d^3 * r) :
    let h:=⌊d * r / 10⌋₊
    d^3 * r / 5120 ≤ (h:ℝ) * Real.log (1 + (d^2 * r / 64) / ((r:ℝ) * Real.log 2)):=by
  dsimp only
  have hr:0 < (r:ℝ):=by
    by_contra h
    have hr0:(r:ℝ) = 0:=le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hr0,mul_zero] at cQ
    norm_num at cQ
  have WH:(1/2:ℝ) ≤ Real.log 2:=by linarith [Real.log_two_gt_d9]
  have WI:Real.log 2 ≤ 1:=by linarith [Real.log_two_lt_d9]
  have hlog:0 < Real.log 2:=lt_of_lt_of_le (by norm_num) WH
  have Zk:d ≤ 1:=by linarith
  have hsq:d^2 ≤ 1:=by nlinarith
  have hdr:d^3 * r ≤ d * r:=by
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hsq)]) hr.le
  have hfloor:d * r / 20 ≤ (⌊d * r / 10⌋₊:ℝ):=by
    have hh:=Nat.lt_floor_add_one (d * r / 10)
    have Zl:1000 ≤ d * r:=cQ.trans hdr
    linarith
  have heq:(d^2 * r / 64) / ((r:ℝ) * Real.log 2) = d^2 / (64 * Real.log 2):=by
    field_simp
  let δ:=d^2 / (64 * Real.log 2)
  have hδ:0 ≤ δ:=div_nonneg (sq_nonneg _) (by positivity)
  have hδ1:δ ≤ 1:=by
    apply (div_le_iff₀ (mul_pos (by norm_num) hlog)).mpr
    nlinarith
  have XG:d^2 / 64 ≤ δ:=by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlog)).mpr
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr WI)]
  have WJ:δ/2 ≤ Real.log (1+δ):=by
    apply le_trans ?_ (Real.le_log_one_add_of_nonneg hδ)
    apply (le_div_iff₀ (by linarith:0 < δ+2)).mpr
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  rw [heq]
  change _ ≤ (⌊d * r / 10⌋₊:ℝ) * Real.log (1+δ)
  have hm:=mul_le_mul hfloor WJ (by linarith) (Nat.cast_nonneg _)
  have hm':d^3 * r / 2560 ≤ (d*r/20) * (δ/2):=by
    have:=mul_le_mul_of_nonneg_left XG (by positivity:0 ≤ d*r/40)
    nlinarith
  have hnon:0 ≤ d^3 * r:=by positivity
  nlinarith
theorem qz {r d:ℝ} (hr:0 ≤ r) (hd:0 ≤ d) (hd1:d ≤ 1)
    (cQ:1000 ≤ d^3 * r):1000 ≤ d*r:=by
  have hs:d^2 ≤ 1:=by nlinarith
  have hc:d^3 ≤ d:=by nlinarith [mul_nonneg hd (sub_nonneg.mpr hs)]
  exact cQ.trans (mul_le_mul_of_nonneg_right hc hr)
theorem IQ {r:ℕ} {d t u l:ℝ}
    (hd:0 < d) (hd1:d ≤ 1/4) (ht:1/2 ≤ t) (hu:0 ≤ u) (hutu:u ≤ 2*t)
    (hl:(r:ℝ)*t ≤ l) (cQ:1000 ≤ d^3 * r) :
    Real.log 2 + (1-d)*l + (2*⌊d*r/10⌋₊:ℕ)*u < l:=by
  have hdr:1000 ≤ d*r:=qz (Nat.cast_nonneg _) hd.le (by linarith) cQ
  have hf:(⌊d*r/10⌋₊:ℝ) ≤ d*r/10:=Nat.floor_le (by positivity)
  have hm:(2*⌊d*r/10⌋₊:ℕ)*u ≤ (d*r/5)*(2*t):=by
    push_cast
    apply mul_le_mul (by linarith) hutu hu
    positivity
  have hdl:=mul_le_mul_of_nonneg_left hl hd.le
  have hdt:500 ≤ d*r*t:=by
    have hh:=mul_le_mul_of_nonneg_left ht (by positivity:0 ≤ d*r)
    nlinarith
  have hlog:Real.log 2 ≤ 1:=by linarith [Real.log_two_lt_d9]
  nlinarith
theorem FU {r:ℕ} {d t l:ℝ} (hd:0 < d) (hd1:d ≤ 1/4)
    (ht:1/2 ≤ t) (hl:(r:ℝ)*t ≤ l) (cQ:1000 ≤ d^3 * r) :
    d*l/2 ≤ l - ((1-d)*l + Real.log 2/2):=by
  have hdr:1000 ≤ d*r:=qz (Nat.cast_nonneg _) hd.le (by linarith) cQ
  have h1:=mul_le_mul_of_nonneg_left hl hd.le
  have h2:=mul_le_mul_of_nonneg_left ht (by positivity:0 ≤ d*r)
  have hlog:Real.log 2 ≤ 1:=by linarith [Real.log_two_lt_d9]
  nlinarith
theorem uW {r d t l V:ℝ} (hr:0 < r) (hd:0 ≤ d)
    (ht:0 < t) (hl:r*t ≤ l) (hV:0 < V) (Vw:V ≤ r*t^2) :
    2*(d^2*r/64) ≤ (d*l/2)^2 / (2*V):=by
  have hdl:0 ≤ d*r*t/2:=by positivity
  have Vz:d*r*t/2 ≤ d*l/2:=by nlinarith [mul_le_mul_of_nonneg_left hl hd]
  have hs:(d*r*t/2)^2 ≤ (d*l/2)^2:=(sq_le_sq₀ hdl (hdl.trans Vz)).mpr Vz
  have hden:0 < 2*r*t^2:=by positivity
  calc
    2*(d^2*r/64) ≤ d^2*r/8:=by nlinarith [mul_nonneg (sq_nonneg d) hr.le]
    _ = (d*r*t/2)^2 / (2*r*t^2):=by field_simp; ring
    _ ≤ (d*l/2)^2 / (2*r*t^2):=div_le_div_of_nonneg_right hs hden.le
    _ ≤ (d*l/2)^2 / (2*V):=div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
theorem aE.F3 (s:aE) :
    Real.log (s.period:ℝ) = ∑ p:s.primes,Real.log (p:ℝ):=by
  classical
  unfold aE.period
  push_cast
  rw [Real.log_prod (fun p hp=>by
    exact_mod_cast (s.iF p hp).ne_zero)]
  exact (Finset.sum_coe_sort s.primes (fun p=>Real.log (p:ℝ))).symm
noncomputable def aE.Dr (s:aE):ℝ :=
  ∑ p:s.primes,(((‖Real.log (p:ℝ)‖₊ / 2)^2:ℝ≥0):ℝ)
theorem aE.Np (s:aE) (hr:0 < s.primes.card) :
    0 < s.Dr:=by
  classical
  obtain ⟨p,hp⟩:=Finset.card_pos.mp hr
  have hlog:0 < Real.log (p:ℝ):=Real.log_pos (by exact_mod_cast (s.iF p hp).one_lt)
  apply Finset.sum_pos' (fun _ _=>by positivity)
  refine ⟨⟨p,hp⟩,Finset.mem_univ _,?_⟩
  simp only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,coe_nnnorm,Real.norm_eq_abs,
    abs_of_pos hlog]
  positivity
theorem aE.Ol (s:aE) {U:ℝ}
    (hU:1 ≤ U) (hpU:∀ p ∈ s.primes,(p:ℝ) ≤ U) :
    s.Dr ≤ (s.primes.card:ℝ) * (Real.log U / 2)^2:=by
  classical
  calc
    _ ≤ ∑ _p:s.primes,(Real.log U / 2)^2:=by
      apply Finset.sum_le_sum
      intro p _
      have hp:0 < (p:ℝ):=by exact_mod_cast (s.iF p p.property).pos
      have hlog:0 ≤ Real.log (p:ℝ):=Real.log_nonneg (by exact_mod_cast (s.iF p p.property).one_le)
      have hle:=Real.log_le_log hp (hpU p p.property)
      simp only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,coe_nnnorm,Real.norm_eq_abs,
        abs_of_nonneg hlog]
      exact (sq_le_sq₀ (by positivity) (div_nonneg (Real.log_nonneg hU) (by norm_num))).mpr (by linarith)
    _ = _:=by simp [nsmul_eq_mul]
theorem aE.LX (s:aE)
    {T R W d:ℝ} {e:ℂ} (he:‖e‖ = 1) (hT:5 ≤ T)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hW:1 ≤ W) (q8:W ≤ R) (hd:0 < d) (hd1:d < 1/4)
    (Qc:R*W ≤ (s.period:ℝ)^(1-d)) (cQ:1000 ≤ d^3*s.primes.card) :
    (gY s.primes).real {σ | s.kG (gC e R W) σ} ≤
      Real.exp (-(d^3*s.primes.card/5120)):=by
  have hr:0 < s.primes.card:=by
    by_contra h
    have hz:s.primes.card = 0:=Nat.eq_zero_of_not_pos h
    rw [hz,Nat.cast_zero,mul_zero] at cQ
    norm_num at cQ
  have hr':0 < (s.primes.card:ℝ):=by exact_mod_cast hr
  have hP:0 < (s.period:ℝ):=by exact_mod_cast s.period_pos
  have o9:0 < T:=by linarith
  have hU:1 ≤ 2*T:=by linarith
  have Uj:0 < 2*T:=by linarith
  have Qd:0 < W:=by linarith
  have Qe:0 < R:=lt_of_lt_of_le Qd q8
  have Uk:0 < R*W:=mul_pos Qe Qd
  have KR:1/2 ≤ Real.log T:=by
    have Qn:=Real.log_le_log (by norm_num:(0:ℝ) < 2) (by linarith:2 ≤ T)
    linarith [Real.log_two_gt_d9]
  have WK:Real.log (2*T) ≤ 2*Real.log T:=by
    rw [Real.log_mul (by norm_num) o9.ne']
    have hh:=Real.log_le_log (by norm_num:(0:ℝ) < 2) (by linarith:2 ≤ T)
    linarith
  have Qg:(s.primes.card:ℝ)*Real.log T ≤ Real.log (s.period:ℝ):=by
    rw [s.F3]
    calc
      _ = ∑ _p:s.primes,Real.log T:=by simp [nsmul_eq_mul]
      _ ≤ _:=Finset.sum_le_sum (fun p _=>Real.log_le_log o9 (hpT p p.property).1)
  have XH:0 < Real.log (s.period:ℝ) :=
    (mul_pos hr' (by linarith:0 < Real.log T)).trans_le Qg
  have VA:R ≤ R*W:=by nlinarith
  have Zb:Real.log R ≤ (1-d)*Real.log (s.period:ℝ):=by
    have hh:=Real.log_le_log Qe (VA.trans Qc)
    simpa only [Real.log_rpow hP] using hh
  have WL:Real.log (2*R*W) ≤ Real.log 2 + (1-d)*Real.log (s.period:ℝ):=by
    have hh:=Real.log_le_log Uk Qc
    rw [Real.log_rpow hP] at hh
    have heq:2*R*W = 2*(R*W):=by ring
    rw [heq,Real.log_mul (by norm_num) Uk.ne']
    linarith
  have Zd:Real.log (2*R^2)/2 ≤ (1-d)*Real.log (s.period:ℝ) + Real.log 2/2:=by
    rw [Real.log_mul (by norm_num) (pow_pos Qe 2).ne',Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  let h:ℕ:=⌊d*s.primes.card/10⌋₊
  have jd:(2*R*W) * (2*T)^(2*h) < (s.period:ℝ):=by
    apply (Real.log_lt_log_iff (mul_pos (by positivity) (pow_pos Uj _)) hP).mp
    rw [Real.log_mul (by positivity:2*R*W ≠ 0) (pow_pos Uj _).ne',Real.log_pow]
    have hh:=IQ hd hd1.le KR (Real.log_nonneg hU) WK Qg cQ
    exact (add_le_add_left WL _).trans_lt hh
  have hV:=s.Np hr
  have Vw:s.Dr ≤ (s.primes.card:ℝ)*(Real.log T)^2:=by
    apply (s.Ol hU (fun p hp=>(hpT p hp).2)).trans
    apply mul_le_mul_of_nonneg_left ?_ hr'.le
    apply (sq_le_sq₀ (div_nonneg (Real.log_nonneg hU) (by norm_num)) (by linarith:0 ≤ Real.log T)).mpr
    linarith
  apply s.BW (gC e R W) hr hU
    (fun p hp=>(hpT p hp).2) (by positivity) (fun _ hw _ hw' =>
      vP he Qe.le Qd.le hw hw') jd
    (fun _ hz=>FH he Qd.le q8 hz)
    (ε:=d*Real.log (s.period:ℝ)/2) (a:=d^2*s.primes.card/64) (h:=h)
  · positivity
  · rw [← s.F3]
    have hh:=FU hd hd1.le KR Qg cQ
    linarith
  · positivity
  · have hc:d^3 ≤ d^2:=by nlinarith [sq_nonneg d,mul_nonneg (sq_nonneg d) (by linarith:0 ≤ 1-d)]
    have hh:=mul_le_mul_of_nonneg_right hc hr'.le
    nlinarith [mul_nonneg (sq_nonneg d) hr'.le]
  · exact uW hr' hd.le (by linarith) Qg hV Vw
  · exact Ek hd hd1.le cQ
end GaussianMoat
end OAI
end
section
namespace OAI
universe cD dD g4 bU oG
namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal
open scoped BigOperators
open scoped Classical
noncomputable def eo {α:Type cD} [Fintype α] (p:α → ℝ):ℝ :=
  ∑ a,Real.negMulLog (p a)
theorem Ds {p q:ℝ} (hp:0 ≤ p) (hq:0 ≤ q) (habs:q = 0 → p = 0) :
    p - q ≤ p * (Real.log p - Real.log q):=by
  by_cases hp0:p = 0
  · simp [hp0,hq]
  have hpp:0 < p:=lt_of_le_of_ne hp (Ne.symm hp0)
  have hqp:0 < q:=lt_of_le_of_ne hq (Ne.symm (fun h=>hp0 (habs h)))
  have h:=mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  rw [Real.log_div hp0 hqp.ne'] at h
  have h1:q*(p/q-1) = p-q:=by field_simp
  have h2:q*(p/q*(Real.log p-Real.log q)) = p*(Real.log p-Real.log q):=by field_simp
  rwa [h1,h2] at h
theorem O5 {α:Type cD} [Fintype α] (p q:α → ℝ)
    (hp:∀ a,0 ≤ p a) (hq:∀ a,0 ≤ q a)
    (habs:∀ a,q a = 0 → p a = 0) (hsum:∑ a,p a = ∑ a,q a) :
    0 ≤ ∑ a,p a * (Real.log (p a) - Real.log (q a)):=by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun a _=>Ds (hp a) (hq a) (habs a))
  simpa [Finset.sum_sub_distrib,hsum] using h
theorem yD {α:Type cD} {β:Type dD} [Fintype α] [Fintype β]
    (p:α → β → ℝ) (hp:∀ a b,0 ≤ p a b) :
    (∑ a,∑ b,Real.negMulLog (p a b)) + Real.negMulLog (∑ a,∑ b,p a b) ≤
      (∑ a,Real.negMulLog (∑ b,p a b)) + ∑ b,Real.negMulLog (∑ a,p a b):=by
  classical
  let r:=fun a=>∑ b,p a b
  let c:=fun b=>∑ a,p a b
  let m:=∑ a,r a
  have hr:∀ a,0 ≤ r a:=fun a=>Finset.sum_nonneg (fun b _=>hp a b)
  have hc:∀ b,0 ≤ c b:=fun b=>Finset.sum_nonneg (fun a _=>hp a b)
  have hm:0 ≤ m:=Finset.sum_nonneg (fun a _=>hr a)
  have hpr:∀ a b,p a b ≤ r a:=fun a b =>
    Finset.single_le_sum (fun b' _=>hp a b') (Finset.mem_univ b)
  have hpc:∀ a b,p a b ≤ c b:=fun a b =>
    Finset.single_le_sum (fun a' _=>hp a' b) (Finset.mem_univ a)
  have hrm:∀ a,r a ≤ m:=fun a =>
    Finset.single_le_sum (fun a' _=>hr a') (Finset.mem_univ a)
  have hcm:∑ b,c b = m:=Finset.sum_comm
  by_cases hm0:m = 0
  · have hz:∀ a b,p a b = 0:=fun a b=>le_antisymm (by simpa [hm0] using (hpr a b).trans (hrm a)) (hp a b)
    simp [hz]
  have hmp:0 < m:=lt_of_le_of_ne hm (Ne.symm hm0)
  let q:=fun ab:α × β=>r ab.1 * c ab.2 / m
  have hq:∀ ab,0 ≤ q ab:=fun ab=>div_nonneg (mul_nonneg (hr _) (hc _)) hm
  have habs:∀ ab:α × β,q ab = 0 → p ab.1 ab.2 = 0:=by
    intro ab hh
    by_contra h
    have hpp:0 < p ab.1 ab.2:=lt_of_le_of_ne (hp _ _) (Ne.symm h)
    have hrp:0 < r ab.1:=hpp.trans_le (hpr _ _)
    have hcp:0 < c ab.2:=hpp.trans_le (hpc _ _)
    exact (div_pos (mul_pos hrp hcp) hmp).ne' hh
  have WM:∑ ab,q ab = m:=by
    rw [Fintype.sum_prod_type]
    change (∑ a,∑ b,r a*c b/m) = m
    have hi:∀ a,(∑ b,r a*c b/m) = r a:=by
      intro a
      calc
        _ = (r a*(∑ b,c b))/m:=by rw [Finset.mul_sum,Finset.sum_div]
        _ = r a:=by rw [hcm,mul_div_cancel_right₀ _ hm0]
    simp_rw [hi]
    rfl
  have hg:=O5 (fun ab:α × β=>p ab.1 ab.2) q (fun _=>hp _ _) hq habs
    (by rw [WM,Fintype.sum_prod_type])
  have ht:∀ a b,p a b * (Real.log (p a b) - Real.log (q (a,b))) =
      p a b*Real.log (p a b) - p a b*Real.log (r a) - p a b*Real.log (c b) + p a b*Real.log m:=by
    intro a b
    by_cases hz:p a b = 0
    · simp [hz]
    have hpp:0 < p a b:=lt_of_le_of_ne (hp _ _) (Ne.symm hz)
    have hrp:0 < r a:=hpp.trans_le (hpr _ _)
    have hcp:0 < c b:=hpp.trans_le (hpc _ _)
    dsimp [q]
    rw [Real.log_div (mul_pos hrp hcp).ne' hm0,Real.log_mul hrp.ne' hcp.ne']
    ring
  have hrow:(∑ a,∑ b,p a b * Real.log (r a)) = ∑ a,r a*Real.log (r a):=by
    simp_rw [← Finset.sum_mul]
    rfl
  have hcol:(∑ a,∑ b,p a b * Real.log (c b)) = ∑ b,c b*Real.log (c b):=by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rfl
  have XL:(∑ a,∑ b,p a b * Real.log m) = m*Real.log m:=by
    simp_rw [← Finset.sum_mul]
    rfl
  rw [Fintype.sum_prod_type] at hg
  simp_rw [ht,Finset.sum_add_distrib,Finset.sum_sub_distrib] at hg
  rw [hrow,hcol,XL] at hg
  change (∑ a,∑ b,Real.negMulLog (p a b)) + Real.negMulLog m ≤
    (∑ a,Real.negMulLog (r a)) + ∑ b,Real.negMulLog (c b)
  simp only [Real.negMulLog,neg_mul,Finset.sum_neg_distrib]
  linarith
theorem LY {α:Type cD} [Fintype α] (p:α → ℝ) (hp:∀ a,0 ≤ p a) :
    Real.negMulLog (∑ a,p a) ≤ ∑ a,Real.negMulLog (p a):=by
  have ht:∀ a,-p a * Real.log (∑ b,p b) ≤ Real.negMulLog (p a):=by
    intro a
    by_cases hz:p a = 0
    · simp [hz]
    have hpos:=lt_of_le_of_ne (hp a) (Ne.symm hz)
    have hle:p a ≤ ∑ b,p b:=Finset.single_le_sum (fun b _=>hp b) (Finset.mem_univ a)
    have hh:=mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) (hp a)
    unfold Real.negMulLog
    linarith
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun a _=>ht a)
  simpa only [← Finset.sum_mul,Finset.sum_neg_distrib,Real.negMulLog] using hh
structure aD (α:Type cD) [Fintype α] where
  mass:α → ℝ
  nonneg:∀ a,0 ≤ mass a
  dN:∑ a,mass a = 1
namespace aD
variable {α:Type cD} {β:Type dD} {γ:Type g4} {Ω:Type bU} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω]
instance:CoeFun (aD α) (fun _=>α → ℝ):=⟨mass⟩
theorem ext {p q:aD α} (h:∀ a,p a = q a):p = q:=by
  cases p; cases q; congr; exact funext h
theorem le_one (p:aD α) (a:α):p a ≤ 1:=by
  rw [← p.dN]
  exact Finset.single_le_sum (fun x _=>p.nonneg x) (Finset.mem_univ a)
theorem nonempty (p:aD α):Nonempty α:=by
  by_contra h
  have:IsEmpty α:=not_nonempty_iff.mp h
  simpa using p.dN
noncomputable def entropy (p:aD α):ℝ:=eo p
theorem Om (p:aD α):0 ≤ p.entropy :=
  Finset.sum_nonneg (fun a _=>Real.negMulLog_nonneg (p.nonneg a) (p.le_one a))
theorem lK (p:aD α):p.entropy ≤ Real.log (Fintype.card α):=by
  have:=p.nonempty
  have hn:0 < (Fintype.card α:ℝ):=by exact_mod_cast Fintype.card_pos
  have h:=O5 (fun a=>p a) (fun _=>(Fintype.card α:ℝ)⁻¹) p.nonneg
    (fun _=>by positivity) (fun _ h=>False.elim ((inv_pos.mpr hn).ne' h)) (by simp [p.dN,hn.ne'])
  have heq:(∑ a,p a * (Real.log (p a) - Real.log (Fintype.card α:ℝ)⁻¹)) =
      -p.entropy + Real.log (Fintype.card α):=by
    simp only [Real.log_inv,sub_neg_eq_add,mul_add,Finset.sum_add_distrib,
      ← Finset.sum_mul,p.dN,one_mul,entropy,eo,Real.negMulLog]
    rw [← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq] at h
  linarith
noncomputable def map (p:aD α) (f:α → β):aD β:=by
  classical
  exact {
    mass:=fun b=>∑ a,if f a = b then p a else 0
    nonneg:=fun b=>Finset.sum_nonneg (fun a _=>by split_ifs; exact p.nonneg a; exact le_rfl)
    dN:=by rw [Finset.sum_comm]; simpa using p.dN }
@[simp] theorem f7 (p:aD α) (f:α → β) (b:β) :
    p.map f b = ∑ a,if f a = b then p a else 0:=by
  classical
  rfl
@[simp] theorem map_id (p:aD α):p.map id = p:=by
  classical
  apply aD.ext; rintro a
  simp
@[simp] theorem map_comp (p:aD α) (f:α → β) (g:β → γ) :
    (p.map f).map g = p.map (g ∘ f):=by
  classical
  apply aD.ext; rintro c
  simp only [f7]
  have he (b:β):(if g b = c then ∑ a,if f a = b then p a else 0 else 0) =
      ∑ a,if f a = b ∧ g b = c then p a else 0:=by
    by_cases h:g b = c <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_and]
noncomputable def H (p:aD Ω) (X:Ω → α):ℝ:=(p.map X).entropy
noncomputable def g7 (p:aD Ω) (X:Ω → α) (Y:Ω → β):ℝ :=
  p.H (fun ω=>(X ω,Y ω)) - p.H Y
theorem F5 (p:aD Ω) (X:Ω → α) :
    p.H X = -∑ ω,p ω * Real.log (p.map X (X ω)):=by
  classical
  unfold H entropy eo
  simp only [Real.negMulLog,neg_mul,Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∑ a,∑ ω,(if X ω = a then p ω else 0) * Real.log (p.map X a):=by
      apply Finset.sum_congr rfl
      intro a _
      rw [f7,Finset.sum_mul]
    _ = _:=by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      simp [ite_mul]
theorem k8 (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (hf:∀ ω ω',X ω = X ω' ↔ Y ω = Y ω'):p.H X = p.H Y:=by
  rw [F5,F5]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  have hh:p.map X (X ω) = p.map Y (Y ω):=by
    simp only [f7]
    apply Finset.sum_congr rfl
    intro ω' _
    rw [hf]
  rw [hh]
theorem Tx (p:aD Ω) (X:Ω → α) (f:α → β)
    (hf:Function.Injective f):p.H (f ∘ X) = p.H X :=
  p.k8 _ _ (fun _ _=>hf.eq_iff)
theorem Dt (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.H (fun ω=>(X ω,Y ω)) = p.H (fun ω=>(Y ω,X ω)):=by
  apply p.k8
  simp only [Prod.mk.injEq,and_comm,implies_true]
theorem VE (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.H (fun ω=>(X ω,(Y ω,Z ω))) = p.H (fun ω=>((X ω,Y ω),Z ω)):=by
  apply p.k8
  simp only [Prod.mk.injEq,and_assoc,implies_true]
theorem Um (p:aD Ω) (X:Ω → α) (f:α → β) :
    p.H (fun ω=>(X ω,f (X ω))) = p.H X:=by
  apply p.k8
  intro ω ω'
  simp only [Prod.mk.injEq]
  exact ⟨And.left,fun h=>⟨h,congrArg f h⟩⟩
@[simp] theorem WO (p:aD Ω) (X:Ω → α) (f:α → β) :
    (p.map X).H f = p.H (f ∘ X):=by simp [H]
@[simp] theorem Qo (p:aD (α × β)) (a:α) :
    p.map Prod.fst a = ∑ b,p (a,b):=by
  rw [f7,Fintype.sum_prod_type,Finset.sum_comm]
  simp
@[simp] theorem oH (p:aD (α × β)) (b:β) :
    p.map Prod.snd b = ∑ a,p (a,b):=by
  simp [f7,Fintype.sum_prod_type]
theorem Oo (p:aD (α × β)):(p.map Prod.snd).entropy ≤ p.entropy:=by
  have h:=Finset.sum_le_sum (s:=Finset.univ)
    (fun b _=>LY (fun a=>p (a,b)) (fun _=>p.nonneg _))
  rw [Finset.sum_comm] at h
  simpa only [entropy,eo,oH,Fintype.sum_prod_type] using h
theorem Oq (p:aD (α × β)) :
    p.entropy ≤ (p.map Prod.fst).entropy + (p.map Prod.snd).entropy:=by
  have h:=yD (fun a b=>p (a,b)) (fun _ _=>p.nonneg _)
  have hs:(∑ a,∑ b,p (a,b)) = 1:=by simpa only [Fintype.sum_prod_type] using p.dN
  rw [hs,Real.negMulLog_one,add_zero] at h
  simpa only [entropy,eo,Qo,oH,Fintype.sum_prod_type] using h
theorem qL (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.H Y ≤ p.H (fun ω=>(X ω,Y ω)):=by
  have h:=(p.map (fun ω=>(X ω,Y ω))).Oo
  simpa only [map_comp,Function.comp_def,H] using h
theorem wR (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.H (fun ω=>(X ω,Y ω)) ≤ p.H X + p.H Y:=by
  have h:=(p.map (fun ω=>(X ω,Y ω))).Oq
  simpa only [map_comp,Function.comp_def,H] using h
theorem VF (p:aD Ω) (X:Ω → α) (Y:Ω → β):0 ≤ p.g7 X Y :=
  sub_nonneg.mpr (p.qL X Y)
theorem RH (p:aD Ω) (X:Ω → α) (Y:Ω → β):p.g7 X Y ≤ p.H X:=by
  have h:=p.wR X Y
  unfold g7
  linarith
theorem Ot (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.H X ≤ p.g7 X Y + p.H Y:=by
  have h:=p.qL Y X
  rw [p.Dt Y X] at h
  simpa only [g7,sub_add_cancel] using h
theorem El (p:aD (α × (β × γ))) :
    p.entropy + (p.map (fun x=>x.2.1)).entropy ≤
      (p.map (fun x=>(x.1,x.2.1))).entropy + (p.map Prod.snd).entropy:=by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    yD (fun a c=>p (a,(b,c))) (fun _ _=>p.nonneg _))
  have hmid (b:β):p.map (fun x=>x.2.1) b = ∑ a,∑ c,p (a,(b,c)):=by
    simp only [f7,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp
  have hleft (a:α) (b:β):p.map (fun x=>(x.1,x.2.1)) (a,b) = ∑ c,p (a,(b,c)):=by
    simp [f7,Fintype.sum_prod_type,Prod.mk.injEq,ite_and]
    rw [Finset.sum_comm]
    simp
  have RI:(∑ b,∑ a,∑ c,Real.negMulLog (p (a,(b,c)))) = p.entropy:=by
    rw [Finset.sum_comm]
    simp only [entropy,eo,Fintype.sum_prod_type]
  have hxy:(∑ b,∑ a,Real.negMulLog (∑ c,p (a,(b,c)))) =
      (p.map (fun x=>(x.1,x.2.1))).entropy:=by
    rw [Finset.sum_comm]
    simp only [entropy,eo,Fintype.sum_prod_type,hleft]
  simp only [Finset.sum_add_distrib] at h
  rw [RI,hxy] at h
  simpa only [entropy,eo,Fintype.sum_prod_type,hmid,oH] using h
theorem CY (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.H (fun ω=>(X ω,(Y ω,Z ω))) + p.H Y ≤
      p.H (fun ω=>(X ω,Y ω)) + p.H (fun ω=>(Y ω,Z ω)):=by
  have h:=(p.map (fun ω=>(X ω,(Y ω,Z ω)))).El
  simpa only [map_comp,Function.comp_def,H] using h
theorem RJ (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.g7 X (fun ω=>(Y ω,Z ω)) ≤ p.g7 X Y:=by
  have h:=p.CY X Y Z
  unfold g7
  linarith
noncomputable def RK (p:aD Ω) (X:Ω → α) (Y:Ω → β):ℝ :=
  p.H X - p.g7 X Y
noncomputable def En {δ:Type oG} [Fintype δ] (p:aD Ω)
    (X:Ω → α) (Y:Ω → β) (Z:Ω → δ):ℝ :=
  p.g7 X Z - p.g7 X (fun ω=>(Y ω,Z ω))
theorem Tk (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    0 ≤ p.RK X Y:=sub_nonneg.mpr (p.RH X Y)
theorem Nq (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.g7 X (fun ω=>(Y ω,Z ω)) = p.g7 X (fun ω=>(Z ω,Y ω)):=by
  unfold g7
  congr 1
  · apply p.k8
    simp only [Prod.mk.injEq,and_comm,implies_true]
  · exact p.Dt Y Z
theorem Rw (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    0 ≤ p.En X Y Z:=by
  unfold En
  rw [Nq]
  exact sub_nonneg.mpr (p.RJ X Z Y)
theorem LZ (p:α → ℝ) (c:ℝ) :
    eo (fun a=>c*p a) = c*eo p + (∑ a,p a)*Real.negMulLog c:=by
  simp only [eo,Real.negMulLog_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.sum_mul]
  ring
theorem vQ (p:α → ℝ) (hp:∀ a,0 ≤ p a) :
    eo p ≤ (∑ a,p a)*Real.log (Fintype.card α) + Real.negMulLog (∑ a,p a):=by
  let m:=∑ a,p a
  have hm:0 ≤ m:=Finset.sum_nonneg (fun a _=>hp a)
  by_cases hm0:m = 0
  · have hz:∀ a,p a = 0:=by
      intro a
      have hle:p a ≤ m:=Finset.single_le_sum (fun b _=>hp b) (Finset.mem_univ a)
      exact le_antisymm (by simpa [hm0] using hle) (hp a)
    simp [eo,hz]
  let q:aD α:={
    mass:=fun a=>p a/m
    nonneg:=fun a=>div_nonneg (hp a) hm
    dN:=by rw [← Finset.sum_div]; exact div_self hm0 }
  have h:=mul_le_mul_of_nonneg_left q.lK hm
  have he:eo p = m*q.entropy + Real.negMulLog m:=by
    have hs:(fun a=>m*q a) = p:=by ext a; dsimp [q]; field_simp
    rw [← hs,LZ,q.dN,one_mul]
    rfl
  rw [he]
  exact add_le_add_left h _
theorem rW (p:α → ℝ) (hp:∀ a,0 ≤ p a)
    (S:Finset α) (hs:∀ a,a ∉ S → p a = 0) :
    eo p ≤ (∑ a,p a)*Real.log S.card + Real.negMulLog (∑ a,p a):=by
  classical
  have he:eo p = eo (fun a:S=>p a):=by
    unfold eo
    rw [← Finset.sum_subtype S (fun _=>Iff.rfl) (fun a=>Real.negMulLog (p a))]
    exact (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha=>by rw [hs a ha,Real.negMulLog_zero])).symm
  have hm:(∑ a,p a) = ∑ a:S,p a:=by
    rw [← Finset.sum_subtype S (fun _=>Iff.rfl) p]
    exact (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha=>hs a ha)).symm
  rw [he,hm]
  simpa using vQ (fun a:S=>p a) (fun a=>hp a)
theorem z9 (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (L:β → Finset α) (hs:∀ ω,p ω ≠ 0 → X ω ∈ L (Y ω)) :
    p.g7 X Y ≤ ∑ b,p.map Y b * Real.log (L b).card:=by
  classical
  let q:=p.map (fun ω=>(X ω,Y ω))
  have hzero:∀ b a,a ∉ L b → q (a,b) = 0:=by
    intro b a ha
    change p.map (fun ω=>(X ω,Y ω)) (a,b) = 0
    rw [f7]
    apply Finset.sum_eq_zero
    intro ω _
    split_ifs with he
    · have he':=Prod.mk.inj he
      by_contra hn
      have hmem:=hs ω hn
      rw [he'.1,he'.2] at hmem
      exact ha hmem
    · rfl
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    rW (fun a=>q (a,b)) (fun a=>q.nonneg _) (L b) (hzero b))
  have hm (b:β):(∑ a,q (a,b)) = p.map Y b:=by
    rw [← oH,map_comp]
    rfl
  simp_rw [hm] at h
  rw [Finset.sum_add_distrib] at h
  have RI:(∑ b,eo (fun a=>q (a,b))) = p.H (fun ω=>(X ω,Y ω)):=by
    unfold eo
    rw [Finset.sum_comm]
    simp only [H,entropy,eo,Fintype.sum_prod_type,q]
  rw [RI] at h
  change p.g7 X Y ≤ _
  unfold g7
  have hh:(∑ b,Real.negMulLog (p.map Y b)) = p.H Y:=rfl
  rw [hh] at h
  linarith
noncomputable def mix (p:aD Ω) (q:Ω → aD α):aD α:={
  mass:=fun a=>∑ ω,p ω * q ω a
  nonneg:=fun a=>Finset.sum_nonneg (fun ω _=>mul_nonneg (p.nonneg ω) ((q ω).nonneg a))
  dN:=by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum,dN,mul_one]; exact p.dN }
@[simp] theorem kV (p:aD Ω) (q:Ω → aD α) (a:α) :
    p.mix q a = ∑ ω,p ω * q ω a:=rfl
theorem Ou (p:aD Ω) (q:Ω → aD α) :
    (∑ ω,p ω * (q ω).entropy) ≤ (p.mix q).entropy:=by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun a _ =>
    Real.concaveOn_negMulLog.le_map_sum (fun ω _=>p.nonneg ω) p.dN
      (fun ω _=>(q ω).nonneg a))
  change (∑ ω,p ω * ∑ a,Real.negMulLog (q ω a)) ≤ _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simpa only [entropy,eo,kV,smul_eq_mul] using h
@[simp] theorem Yt (p:aD Ω) (a:α):p.H (fun _=>a) = 0:=by
  rw [F5]
  simp [p.dN]
theorem VJ (p:aD Ω) (E:Ω → Bool) :
    p.H E = Real.binEntropy (p.map E true):=by
  have hs:=(p.map E).dN
  simp only [Fintype.sum_bool] at hs
  have hf:p.map E false = 1 - p.map E true:=by linarith
  simp only [H,entropy,eo,Fintype.sum_bool,hf,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
theorem Nr (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.g7 X Y ≤ p.H Z + p.g7 X (fun ω=>(Y ω,Z ω)):=by
  have h1:=p.qL Z (fun ω=>(X ω,Y ω))
  have he:p.H (fun ω=>(Z ω,(X ω,Y ω))) = p.H (fun ω=>(X ω,(Y ω,Z ω))):=by
    apply p.k8
    simp only [Prod.mk.injEq]
    tauto
  rw [he] at h1
  have h2:=p.wR Y Z
  unfold g7
  linarith
omit [Fintype α] in
theorem L6 (S:Finset α) {b:ℝ} (hb:1 ≤ b) (hs:(S.card:ℝ) ≤ b) :
    Real.log S.card ≤ Real.log b:=by
  by_cases hz:S.card = 0
  · simpa [hz] using Real.log_nonneg hb
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hs
theorem Nt (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (L:β → Finset α) (E:Ω → Bool) {b:ℝ} (hb:1 ≤ b)
    (hs:∀ ω,p ω ≠ 0 → E ω = true → X ω ∈ L (Y ω) ∧ ((L (Y ω)).card:ℝ) ≤ b) :
    p.g7 X Y ≤ Real.binEntropy (p.map E true) +
      p.map E true * Real.log b + (1-p.map E true)*Real.log (Fintype.card α):=by
  classical
  let L':β × Bool → Finset α:=fun ye =>
    if ye.2 = true then if ((L ye.1).card:ℝ) ≤ b then L ye.1 else ∅ else Finset.univ
  have hs':∀ ω,p ω ≠ 0 → X ω ∈ L' (Y ω,E ω):=by
    intro ω hn
    by_cases he:E ω = true
    · have hh:=hs ω hn he
      simpa [L',he,hh.2] using hh.1
    · simp [L',he]
  have hc:=p.z9 X (fun ω=>(Y ω,E ω)) L' hs'
  have hcard (y:β) (e:Bool) :
      Real.log (L' (y,e)).card ≤ if e = true then Real.log b else Real.log (Fintype.card α):=by
    cases e
    · simp [L']
    · simp only [L',ite_true]
      split_ifs with hh
      · exact L6 _ hb hh
      · simpa using Real.log_nonneg hb
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun ye _ =>
    mul_le_mul_of_nonneg_left (hcard ye.1 ye.2) ((p.map (fun ω=>(Y ω,E ω))).nonneg ye))
  have hm (e:Bool):(∑ y,p.map (fun ω=>(Y ω,E ω)) (y,e)) = p.map E e:=by
    rw [← oH,map_comp]
    rfl
  have hsum:(∑ ye:β × Bool,p.map (fun ω=>(Y ω,E ω)) ye *
      (if ye.2 = true then Real.log b else Real.log (Fintype.card α))) =
      p.map E true*Real.log b + (1-p.map E true)*Real.log (Fintype.card α):=by
    rw [Fintype.sum_prod_type,Finset.sum_comm,Fintype.sum_bool]
    simp only [Bool.false_eq_true,ite_false,ite_true,← Finset.sum_mul,hm]
    have Aa:=(p.map E).dN
    simp only [Fintype.sum_bool] at Aa
    congr 2
    linarith
  rw [hsum] at hh
  have h:=p.Nr X Y E
  rw [VJ] at h
  linarith
theorem JM (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (L:β → Finset α) (E:Ω → Bool) {b:ℝ} (hb:1 ≤ b)
    (hs:∀ ω,p ω ≠ 0 → E ω = true → X ω ∈ L (Y ω) ∧ ((L (Y ω)).card:ℝ) ≤ b) :
    p.map E true * (Real.log (Fintype.card α) - Real.log b) - Real.binEntropy (p.map E true)
      ≤ Real.log (Fintype.card α) - p.g7 X Y:=by
  have h:=p.Nt X Y L E hb hs
  nlinarith
theorem L7 (p:aD α) (S:Finset α)
    (hs:∀ a ∈ S,p a ≤ 3 / (8 * (Fintype.card α:ℝ))) :
    (S.card:ℝ) / (8 * (Fintype.card α:ℝ)) ≤ Real.log (Fintype.card α) - p.entropy:=by
  classical
  have:=p.nonempty
  have hn:0 < (Fintype.card α:ℝ):=by exact_mod_cast Fintype.card_pos
  let u:ℝ:=(Fintype.card α:ℝ)⁻¹
  have hu:0 < u:=inv_pos.mpr hn
  let d:=fun a=>p a * (Real.log (p a) - Real.log u) - p a + u
  have hd:∀ a,0 ≤ d a:=by
    intro a
    have h:=Ds (p.nonneg a) hu.le (fun hz=>False.elim (hu.ne' hz))
    dsimp [d]
    linarith
  have vG:Real.log 2 ≤ 1:=by have h:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ) < 2); norm_num at h ⊢; exact h
  have kT:∀ a ∈ S,u/8 ≤ d a:=by
    intro a ha
    have h:=Ds (p.nonneg a) (show 0 ≤ u/2 by positivity)
      (fun hz=>False.elim ((div_pos hu (by norm_num:(0:ℝ)<2)).ne' hz))
    rw [Real.log_div hu.ne' (by norm_num:(2:ℝ) ≠ 0)] at h
    have hlog:=mul_le_mul_of_nonneg_left vG (p.nonneg a)
    have hpa:p a ≤ 3*u/8:=by simpa only [u,div_eq_mul_inv,mul_inv_rev,mul_assoc] using hs a ha
    dsimp [d]
    nlinarith
  have hsum:(∑ a,d a) = Real.log (Fintype.card α) - p.entropy:=by
    simp only [d,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ← Finset.sum_mul,p.dN,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,u,Real.log_inv]
    rw [mul_inv_cancel₀ hn.ne']
    simp only [entropy,eo,Real.negMulLog,neg_mul,Finset.sum_neg_distrib]
    ring
  have hh:=Finset.sum_le_sum (s:=S) kT
  have hsub:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _=>hd a)
  have hfinal:=hh.trans hsub
  rw [hsum] at hfinal
  simpa only [Finset.sum_const,nsmul_eq_mul,u,div_eq_mul_inv,mul_inv_rev,mul_assoc] using hfinal
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
section
open scoped BigOperators
def iQ (a b:Fin 3):ℤ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0
def kZ (a b c:Fin 3):Prop:=a ≠ b ∧ b ≠ c ∧ a ≠ c
theorem Ij {a b c:Fin 3} (h:¬ kZ a b c) :
    iQ a b + iQ b c = iQ a c:=by
  unfold kZ at h
  revert a b c
  decide
theorem IT (a b:Fin 3) (ha:a ≠ 0) (hb:b ≠ 0) :
    iQ a b = 0:=by simp [iQ,ha,hb]
theorem JN (a b:Fin 3) (ha:a ≠ 1) (hb:b ≠ 1) :
    iQ a b = 0:=by simp [iQ,ha,hb]
theorem L9 (a b:Fin 3) (ha:a ≠ 2) (hb:b ≠ 2) :
    iQ a b = (b.val:ℤ) - a.val:=by
  revert a b
  decide
theorem wS (c:ℕ → ℕ → Fin 3) (m n:ℕ)
    (pC:∀ i ≤ m,c i 0 = 0)
    (htop:∀ i ≤ m,c i n ≠ 0)
    (hleft:∀ j ≤ n,c 0 j ≠ 2)
    (hright:∀ j ≤ n,c m j ≠ 1) :
    ∃ i < m,∃ j < n,
      kZ (c i j) (c (i+1) j) (c (i+1) (j+1)) ∨
      kZ (c i j) (c i (j+1)) (c (i+1) (j+1)):=by
  by_contra h
  have hcell (i j:ℕ) (hi:i < m) (hj:j < n) :
      iQ (c i j) (c (i+1) j) - iQ (c i (j+1)) (c (i+1) (j+1)) =
      iQ (c i j) (c i (j+1)) - iQ (c (i+1) j) (c (i+1) (j+1)):=by
    have h1:¬ kZ (c i j) (c (i+1) j) (c (i+1) (j+1)) :=
      fun hh=>h ⟨i,hi,j,hj,Or.inl hh⟩
    have h2:¬ kZ (c i j) (c i (j+1)) (c (i+1) (j+1)) :=
      fun hh=>h ⟨i,hi,j,hj,Or.inr hh⟩
    have he1:=Ij h1
    have he2:=Ij h2
    omega
  have hsum:=Finset.sum_congr (s₁:=Finset.range n) rfl (fun j hj =>
    Finset.sum_congr (s₁:=Finset.range m) rfl (fun i hi =>
      hcell i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)))
  have hl:(∑ j ∈ Finset.range n,∑ i ∈ Finset.range m,
      (iQ (c i j) (c (i+1) j) - iQ (c i (j+1)) (c (i+1) (j+1)))) = 0:=by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.sum_range_sub']
    rw [pC i (Nat.le_of_lt (Finset.mem_range.mp hi)),
      pC (i+1) (Finset.mem_range.mp hi)]
    rw [IT _ _ (htop i (Nat.le_of_lt (Finset.mem_range.mp hi)))
      (htop (i+1) (Finset.mem_range.mp hi))]
    rfl
  have hr:(∑ j ∈ Finset.range n,∑ i ∈ Finset.range m,
      (iQ (c i j) (c i (j+1)) - iQ (c (i+1) j) (c (i+1) (j+1)))) = 1:=by
    have he (j:ℕ) (hj:j ∈ Finset.range n) :
        (∑ i ∈ Finset.range m,(iQ (c i j) (c i (j+1)) -
          iQ (c (i+1) j) (c (i+1) (j+1)))) = ((c 0 (j+1)).val:ℤ) - (c 0 j).val:=by
      rw [Finset.sum_range_sub']
      rw [JN _ _ (hright j (Nat.le_of_lt (Finset.mem_range.mp hj)))
        (hright (j+1) (Finset.mem_range.mp hj)),sub_zero,
        L9 _ _ (hleft j (Nat.le_of_lt (Finset.mem_range.mp hj)))
          (hleft (j+1) (Finset.mem_range.mp hj))]
    rw [Finset.sum_congr rfl he,Finset.sum_range_sub (fun j=>((c 0 j).val:ℤ))]
    have RM:c 0 n = 1:=by
      have h0:=htop 0 (Nat.zero_le m)
      have h2:=hleft n le_rfl
      have hone:∀ x:Fin 3,x ≠ 0 → x ≠ 2 → x = 1:=by decide
      exact hone _ h0 h2
    rw [RM,pC 0 (Nat.zero_le m)]
    norm_num
  rw [hl,hr] at hsum
  omega
noncomputable def i6 (z:ℂ):Fin 3:=if z.im < 0 then 0 else if z.re < 0 then 1 else 2
theorem CZ {z:ℂ} (h:i6 z = 0):z.im < 0:=by
  unfold i6 at h
  split_ifs at h with hi hr
  · exact hi
  · exact False.elim ((by decide:(1:Fin 3) ≠ 0) h)
  · exact False.elim ((by decide:(2:Fin 3) ≠ 0) h)
theorem Eo {z:ℂ} (h:i6 z = 1):z.re < 0 ∧ 0 ≤ z.im:=by
  unfold i6 at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide:(0:Fin 3) ≠ 1) h)
  · exact ⟨hr,le_of_not_gt hi⟩
  · exact False.elim ((by decide:(2:Fin 3) ≠ 1) h)
theorem Ep {z:ℂ} (h:i6 z = 2):0 ≤ z.re ∧ 0 ≤ z.im:=by
  unfold i6 at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide:(0:Fin 3) ≠ 2) h)
  · exact False.elim ((by decide:(1:Fin 3) ≠ 2) h)
  · exact ⟨le_of_not_gt hr,le_of_not_gt hi⟩
theorem K6 {a b c:Fin 3} (h:kZ a b c) (q:Fin 3) :
    q = a ∨ q = b ∨ q = c:=by
  unfold kZ at h
  revert a b c q
  decide
theorem q9 {x y z:ℂ} {r:ℝ} (hr:0 ≤ r)
    (hxy:dist x y ≤ r) (hxz:dist x z ≤ r)
    (hc:kZ (i6 x) (i6 y) (i6 z)):‖x‖ ≤ 2*r:=by
  have he (q:Fin 3):∃ w:ℂ,i6 w = q ∧ dist x w ≤ r:=by
    rcases K6 hc q with h | h | h
    · exact ⟨x,h.symm,by simpa using hr⟩
    · exact ⟨y,h.symm,hxy⟩
    · exact ⟨z,h.symm,hxz⟩
  obtain ⟨w0,h0,hd0⟩:=he 0
  obtain ⟨w1,h1,hd1⟩:=he 1
  obtain ⟨w2,h2,hd2⟩:=he 2
  have hc0:=CZ h0
  have hc1:=Eo h1
  have hc2:=Ep h2
  have Xv (w:ℂ) (hd:dist x w ≤ r) : -r ≤ x.re-w.re ∧ x.re-w.re ≤ r:=by
    apply abs_le.mp
    have hh:|x.re-w.re| ≤ dist x w:=by simpa only [Complex.sub_re,dist_eq_norm] using Complex.abs_re_le_norm (x-w)
    exact hh.trans hd
  have hIm (w:ℂ) (hd:dist x w ≤ r) : -r ≤ x.im-w.im ∧ x.im-w.im ≤ r:=by
    apply abs_le.mp
    have hh:|x.im-w.im| ≤ dist x w:=by simpa only [Complex.sub_im,dist_eq_norm] using Complex.abs_im_le_norm (x-w)
    exact hh.trans hd
  have hR1:=Xv w1 hd1
  have hR2:=Xv w2 hd2
  have hI0:=hIm w0 hd0
  have hI1:=hIm w1 hd1
  have hrx:|x.re| ≤ r:=abs_le.mpr ⟨by linarith,by linarith⟩
  have hix:|x.im| ≤ r:=abs_le.mpr ⟨by linarith,by linarith⟩
  have h:=Complex.norm_le_abs_re_add_abs_im x
  linarith
theorem r5 (f:ℕ → ℕ → ℂ) (m n:ℕ) {D:ℝ} (hD:0 ≤ D)
    (Ov:∀ i < m,∀ j ≤ n,dist (f i j) (f (i+1) j) ≤ D)
    (Ow:∀ i ≤ m,∀ j < n,dist (f i j) (f i (j+1)) ≤ D)
    (pC:∀ i ≤ m,(f i 0).im < 0)
    (htop:∀ i ≤ m,0 ≤ (f i n).im)
    (hleft:∀ j ≤ n,(f 0 j).re < 0)
    (hright:∀ j ≤ n,0 ≤ (f m j).re) :
    ∃ i ≤ m,∃ j ≤ n,‖f i j‖ ≤ 4*D:=by
  have hb:∀ i ≤ m,i6 (f i 0) = 0:=by
    intro i hi
    simp [i6,pC i hi]
  have ht:∀ i ≤ m,i6 (f i n) ≠ 0:=by
    intro i hi hh
    exact (not_lt_of_ge (htop i hi)) (CZ hh)
  have hl:∀ j ≤ n,i6 (f 0 j) ≠ 2:=by
    intro j hj hh
    exact (not_le_of_gt (hleft j hj)) (Ep hh).1
  have hr:∀ j ≤ n,i6 (f m j) ≠ 1:=by
    intro j hj hh
    exact (not_lt_of_ge (hright j hj)) (Eo hh).1
  obtain ⟨i,hi,j,hj,hc⟩:=wS (fun i j=>i6 (f i j)) m n hb ht hl hr
  refine ⟨i,hi.le,j,hj.le,?_⟩
  have hdiag:dist (f i j) (f (i+1) (j+1)) ≤ 2*D:=by
    have h:=dist_triangle (f i j) (f (i+1) j) (f (i+1) (j+1))
    have h1:=Ov i hi j hj.le
    have h2:=Ow (i+1) hi j hj
    linarith
  rcases hc with hc | hc
  · have hh:=q9 (show 0 ≤ 2*D by positivity)
      ((Ov i hi j hj.le).trans (by linarith:D ≤ 2*D)) hdiag hc
    linarith
  · have hh:=q9 (show 0 ≤ 2*D by positivity)
      ((Ow i hi.le j hj).trans (by linarith:D ≤ 2*D)) hdiag hc
    linarith
noncomputable def j8 (v:ℕ → ℂ) (n:ℕ) (a:ℂ) (t:ℕ):ℂ :=
  v (t % n) + ((t / n:ℕ):ℂ) * a
@[simp] theorem Uq (v:ℕ → ℂ) (n:ℕ) (a:ℂ) :
    j8 v n a 0 = v 0:=by simp [j8]
@[simp] theorem IU (v:ℕ → ℂ) {n:ℕ} (hn:0 < n) (a:ℂ) (k:ℕ) :
    j8 v n a (k*n) = v 0 + (k:ℂ)*a:=by simp [j8,hn.ne']
theorem C4 (v:ℕ → ℂ) {n:ℕ} (hn:0 < n) (a:ℂ)
    (hv0:v 0 = 0) (hvn:v n = a) {D:ℝ}
    (hstep:∀ i < n,dist (v i) (v (i+1)) ≤ D) (t:ℕ) :
    dist (j8 v n a t) (j8 v n a (t+1)) ≤ D:=by
  have hr:=Nat.mod_lt t hn
  have hdiv:=Nat.mod_add_div t n
  by_cases hh:t % n + 1 = n
  · have ht:t+1 = (t/n+1)*n:=by nlinarith
    rw [ht,IU v hn]
    have he:j8 v n a t = v (t%n) + ((t/n:ℕ):ℂ)*a:=rfl
    rw [he,hv0,zero_add,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (((t/n:ℕ):ℂ)*a) a]
    rw [dist_add_right]
    simpa [hh,hvn] using hstep (t%n) hr
  · have hr':t%n+1 < n:=by omega
    have ht:t+1 = t%n+1+(t/n)*n:=by nlinarith
    have hmod:(t+1)%n = t%n+1:=by rw [ht,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr']
    have XM:(t+1)/n = t/n:=by rw [ht,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hr',zero_add]
    simp only [j8,hmod,XM,dist_add_right]
    exact hstep (t%n) hr
theorem p7 (f:ℕ → ℕ → ℂ) (m n:ℕ) {D:ℝ} (hD:0 ≤ D)
    (Ov:∀ i < m,∀ j ≤ n,dist (f i j) (f (i+1) j) ≤ D)
    (Ow:∀ i ≤ m,∀ j < n,dist (f i j) (f i (j+1)) ≤ D)
    (pC:∀ i ≤ m,0 < (f i 0).im)
    (htop:∀ i ≤ m,(f i n).im ≤ 0)
    (hleft:∀ j ≤ n,(f 0 j).re < 0)
    (hright:∀ j ≤ n,0 ≤ (f m j).re) :
    ∃ i ≤ m,∃ j ≤ n,‖f i j‖ ≤ 4*D:=by
  have hh:∀ i < m,∀ j ≤ n,dist (star (f i j)) (star (f (i+1) j)) ≤ D:=by
    intro i hi j hj
    simpa only [dist_star_star] using Ov i hi j hj
  have hv:∀ i ≤ m,∀ j < n,dist (star (f i j)) (star (f i (j+1))) ≤ D:=by
    intro i hi j hj
    simpa only [dist_star_star] using Ow i hi j hj
  have hb:∀ i ≤ m,(star (f i 0)).im < 0:=by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_lt_zero] using pC i hi
  have ht:∀ i ≤ m,0 ≤ (star (f i n)).im:=by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_nonneg] using htop i hi
  obtain ⟨i,hi,j,hj,hz⟩:=r5 (fun i j=>star (f i j)) m n
    hD hh hv hb ht (by simpa only [Complex.star_def,Complex.conj_re] using hleft)
      (by simpa only [Complex.star_def,Complex.conj_re] using hright)
  exact ⟨i,hi,j,hj,by simpa only [norm_star] using hz⟩
theorem ro (v u:ℕ → ℂ) {n m:ℕ} (hn:0 < n) (hm:0 < m)
    (a b:ℂ) (hv0:v 0 = 0) (hu0:u 0 = 0) (hvn:v n = a) (hum:u m = b)
    (ha:0 < a.re) (hai:a.im = 0) (hb:0 < b.im) {D:ℝ} (hD:0 ≤ D)
    (hv:∀ i < n,dist (v i) (v (i+1)) ≤ D)
    (hu:∀ j < m,dist (u j) (u (j+1)) ≤ D) (w:ℂ) :
    ∃ i < n,∃ j < m,∃ s t:ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D:=by
  let H:ℝ:=(∑ i ∈ Finset.range n,‖v i‖) + (∑ j ∈ Finset.range m,‖u j‖) + ‖w‖
  have hH:0 ≤ H:=by dsimp [H]; positivity
  have hvb (i:ℕ):‖v (i%n)‖ ≤ ∑ k ∈ Finset.range n,‖v k‖ :=
    Finset.single_le_sum (fun k _=>norm_nonneg (v k)) (Finset.mem_range.mpr (Nat.mod_lt i hn))
  have hub (j:ℕ):‖u (j%m)‖ ≤ ∑ k ∈ Finset.range m,‖u k‖ :=
    Finset.single_le_sum (fun k _=>norm_nonneg (u k)) (Finset.mem_range.mpr (Nat.mod_lt j hm))
  have iJ (i j:ℕ):‖v (i%n)-u (j%m)-w‖ ≤ H:=by
    have h1:=norm_sub_le (v (i%n)) (u (j%m))
    have h2:=norm_sub_le (v (i%n)-u (j%m)) w
    dsimp [H]
    linarith [hvb i,hub j]
  have Ur (i j:ℕ) : -H ≤ (v (i%n)-u (j%m)-w).re ∧
      (v (i%n)-u (j%m)-w).re ≤ H :=
    abs_le.mp ((Complex.abs_re_le_norm _).trans (iJ i j))
  have Ut (i j:ℕ) : -H ≤ (v (i%n)-u (j%m)-w).im ∧
      (v (i%n)-u (j%m)-w).im ≤ H :=
    abs_le.mp ((Complex.abs_im_le_norm _).trans (iJ i j))
  obtain ⟨N,hN⟩:=exists_nat_gt (H/b.im)
  have hN':H < (N:ℝ)*b.im:=(div_lt_iff₀ hb).mp hN
  obtain ⟨M,hM⟩:=exists_nat_gt ((H+(N:ℝ)*|b.re|)/a.re)
  have hM':H+(N:ℝ)*|b.re| < (M:ℝ)*a.re:=(div_lt_iff₀ ha).mp hM
  let f (i j:ℕ):ℂ:=j8 v n a i-j8 u m b j-(M:ℂ)*a+(N:ℂ)*b-w
  have hf (i j:ℕ):f i j = v (i%n)-u (j%m)-w +
      (((i/n:ℕ):ℂ)-(M:ℂ))*a + ((N:ℂ)-((j/m:ℕ):ℂ))*b:=by
    dsimp [f,j8]
    ring
  have hfr (i j:ℕ):(f i j).re = (v (i%n)-u (j%m)-w).re +
      (((i/n:ℕ):ℝ)-(M:ℝ))*a.re + ((N:ℝ)-((j/m:ℕ):ℝ))*b.re:=by
    rw [hf]
    simp
  have hfi (i j:ℕ):(f i j).im = (v (i%n)-u (j%m)-w).im +
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.im:=by
    rw [hf]
    simp [hai]
  have Ov (i:ℕ) (_:i < 2*M*n) (j:ℕ) (_:j ≤ 2*N*m) :
      dist (f i j) (f (i+1) j) ≤ D:=by
    simpa only [f,dist_sub_right,dist_add_right] using C4 v hn a hv0 hvn hv i
  have Ow (i:ℕ) (_:i ≤ 2*M*n) (j:ℕ) (_:j < 2*N*m) :
      dist (f i j) (f i (j+1)) ≤ D:=by
    simpa only [f,dist_sub_right,dist_add_right,dist_sub_left] using C4 u hm b hu0 hum hu j
  have pC (i:ℕ) (_:i ≤ 2*M*n):0 < (f i 0).im:=by
    rw [hfi]
    simpa only [Nat.zero_div,Nat.cast_zero,sub_zero] using (show
      0 < (v (i%n)-u (0%m)-w).im+(N:ℝ)*b.im by linarith [(Ut i 0).1])
  have htop (i:ℕ) (_:i ≤ 2*M*n):(f i (2*N*m)).im ≤ 0:=by
    rw [hfi,Nat.mul_div_cancel _ hm,Nat.cast_mul,Nat.cast_ofNat]
    linarith [(Ut i (2*N*m)).2]
  have hcoef (j:ℕ) (hj:j ≤ 2*N*m) :
      |(N:ℝ)-((j/m:ℕ):ℝ)| ≤ N:=by
    have hq:j/m ≤ 2*N:=(Nat.div_le_div_right hj).trans_eq (Nat.mul_div_cancel _ hm)
    have hqr:((j/m:ℕ):ℝ) ≤ 2*(N:ℝ):=by exact_mod_cast hq
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α:=ℝ) (j/m)]⟩
  have hprod (j:ℕ) (hj:j ≤ 2*N*m) :
      -(N:ℝ)*|b.re| ≤ ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ∧
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ≤ (N:ℝ)*|b.re|:=by
    have hh:|((N:ℝ)-((j/m:ℕ):ℝ))*b.re| ≤ (N:ℝ)*|b.re|:=by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoef j hj) (abs_nonneg _)
    simpa only [neg_mul] using abs_le.mp hh
  have hleft (j:ℕ) (hj:j ≤ 2*N*m):(f 0 j).re < 0:=by
    rw [hfr]
    simp only [Nat.zero_div,Nat.cast_zero,zero_sub]
    nlinarith [(Ur 0 j).2,(hprod j hj).2]
  have hright (j:ℕ) (hj:j ≤ 2*N*m):0 ≤ (f (2*M*n) j).re:=by
    rw [hfr,Nat.mul_div_cancel _ hn,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [(Ur (2*M*n) j).1,(hprod j hj).1]
  obtain ⟨i,_,j,_,hz⟩:=p7 f (2*M*n) (2*N*m)
    hD Ov Ow pC htop hleft hright
  refine ⟨i%n,Nat.mod_lt i hn,j%m,Nat.mod_lt j hm,((i/n:ℕ):ℤ)-(M:ℤ),(N:ℤ)-((j/m:ℕ):ℤ),?_⟩
  convert hz using 1
  rw [hf]
  simp only [Int.cast_sub,Int.cast_natCast]
  congr 1
  ring
theorem qP (v u:ℕ → ℂ) {n m:ℕ} (hn:0 < n) (hm:0 < m)
    (a b:ℂ) (hv0:v 0 = 0) (hu0:u 0 = 0) (hvn:v n = a) (hum:u m = b)
    (ha:0 < a.re) (hai:a.im = 0) (hb:b.im ≠ 0) {D:ℝ} (hD:0 ≤ D)
    (hv:∀ i < n,dist (v i) (v (i+1)) ≤ D)
    (hu:∀ j < m,dist (u j) (u (j+1)) ≤ D) (w:ℂ) :
    ∃ i < n,∃ j < m,∃ s t:ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D:=by
  rcases hb.lt_or_gt with hb | hb
  · have hzv:(fun i=>star (v i)) 0 = 0:=by simp [hv0]
    have hzu:(fun i=>star (u i)) 0 = 0:=by simp [hu0]
    have hva:(fun i=>star (v i)) n = star a:=by simp only [hvn]
    have hub:(fun i=>star (u i)) m = star b:=by simp only [hum]
    have hbr:0 < (star b).im:=by simpa using hb
    have hv':∀ i < n,dist (star (v i)) (star (v (i+1))) ≤ D:=by simpa using hv
    have hu':∀ j < m,dist (star (u j)) (star (u (j+1))) ≤ D:=by simpa using hu
    obtain ⟨i,hi,j,hj,s,t,hh⟩:=ro (fun i=>star (v i))
      (fun j=>star (u j)) hn hm (star a) (star b) hzv hzu hva hub
      (by simpa using ha) (by simpa using hai) hbr hD hv' hu' (star w)
    refine ⟨i,hi,j,hj,s,t,?_⟩
    have he:‖star (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)‖ ≤ 4*D:=by
      simpa only [star_sub,star_add,star_mul,star_intCast,mul_comm] using hh
    simpa only [norm_star] using he
  · exact ro v u hn hm a b hv0 hu0 hvn hum ha hai hb hD hv hu w
theorem s9 (v u:ℕ → ℂ) {n m:ℕ} (hn:0 < n) (hm:0 < m)
    (a b:ℂ) (hv0:v 0 = 0) (hu0:u 0 = 0) (hvn:v n = a) (hum:u m = b)
    (ha:a ≠ 0) (hb:(b/a).im ≠ 0) {D:ℝ} (hD:0 ≤ D)
    (hv:∀ i < n,dist (v i) (v (i+1)) ≤ D)
    (hu:∀ j < m,dist (u j) (u (j+1)) ≤ D) (w:ℂ) :
    ∃ i < n,∃ j < m,∃ s t:ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D:=by
  have hna:0 < ‖a‖:=norm_pos_iff.mpr ha
  have hv':∀ i < n,dist (v i/a) (v (i+1)/a) ≤ D/‖a‖:=by
    intro i hi
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hv i hi) hna.le
  have hu':∀ j < m,dist (u j/a) (u (j+1)/a) ≤ D/‖a‖:=by
    intro j hj
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hu j hj) hna.le
  obtain ⟨i,hi,j,hj,s,t,hh⟩:=qP (fun i=>v i/a)
    (fun j=>u j/a) hn hm 1 (b/a) (by simp [hv0]) (by simp [hu0])
    (by simp [hvn,ha]) (by simp [hum]) (by norm_num) (by simp) hb
    (by positivity:0 ≤ D/‖a‖) hv' hu' (w/a)
  refine ⟨i,hi,j,hj,s,t,?_⟩
  have he:v i/a-u j/a+(s:ℂ)*1+(t:ℂ)*(b/a)-w/a =
      (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)/a:=by field_simp
  rw [he,norm_div] at hh
  have hh':=(div_le_iff₀ hna).mp hh
  calc
    _ ≤ 4 * (D/‖a‖) * ‖a‖:=hh'
    _ = 4*D:=by field_simp
end
def nU:GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z:=![z.re,z.im]
  invFun v:=⟨v 0,v 1⟩
  left_inv z:=by ext <;> rfl
  right_inv v:=by ext i; fin_cases i <;> rfl
  map_add' z w:=by ext i; fin_cases i <;> rfl
  map_smul' c z:=by
    ext i
    fin_cases i <;> simp [zsmul_eq_mul]
noncomputable def latticeBasis:Module.Basis (Fin 2) ℤ GaussianInt :=
  (Pi.basisFun ℤ (Fin 2)).map nU.symm
noncomputable instance:Module.Free ℤ GaussianInt:=Module.Free.of_basis latticeBasis
instance:Module.Finite ℤ GaussianInt:=Module.Finite.of_basis latticeBasis
noncomputable def gT (a b:GaussianInt):GaussianInt →ₗ[ℤ] GaussianInt :=
  Matrix.toLin latticeBasis latticeBasis !![a.re,b.re; a.im,b.im]
@[simp] theorem oI (a b z:GaussianInt) :
    gT a b z = z.re • a + z.im • b:=by
  apply nU.injective
  change latticeBasis.repr (gT a b z) = nU (z.re • a+z.im • b)
  rw [gT,Matrix.toLin_apply]
  simp only [map_sum,map_smul,Module.Basis.repr_self]
  ext i
  fin_cases i <;> simp [nU,latticeBasis,zsmul_eq_mul,Fin.sum_univ_two,Pi.basisFun_repr,Matrix.vecHead,Matrix.vecTail] <;> ring
@[simp] theorem Mb (a b:GaussianInt) :
    LinearMap.det (gT a b) = a.re*b.im-a.im*b.re:=by
  rw [← LinearMap.det_toMatrix latticeBasis,gT,LinearMap.toMatrix_toLin]
  simp [Matrix.det_fin_two,mul_comm]
theorem qA {a b:GaussianInt} (h:a.re*b.im-a.im*b.re ≠ 0) :
    Function.Injective (gT a b):=by
  intro z w hzw
  have h1:=congrArg Zsqrtd.re hzw
  have h2:=congrArg Zsqrtd.im hzw
  simp only [oI,zsmul_eq_mul,Zsqrtd.re_add,Zsqrtd.im_add,
    Zsqrtd.re_smul,Zsqrtd.im_smul] at h1 h2
  have hr:(a.re*b.im-a.im*b.re)*(z.re-w.re) = 0:=by linear_combination b.im*h1-b.re*h2
  have hi:(a.re*b.im-a.im*b.re)*(z.im-w.im) = 0:=by linear_combination a.re*h2-a.im*h1
  ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left h)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left h)
theorem nV {a b:GaussianInt} (h:a.re*b.im-a.im*b.re ≠ 0) :
    Nat.card (GaussianInt ⧸ (gT a b).range) = (a.re*b.im-a.im*b.re).natAbs:=by
  have hh:=Submodule.natAbs_det_equiv (gT a b).range
    (LinearEquiv.ofInjective (gT a b) (qA h))
  have he:(gT a b).range.subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((LinearEquiv.ofInjective (gT a b)
        (qA h)):GaussianInt →+ (gT a b).range) = gT a b:=by
    ext z <;> rfl
  rw [he,Mb] at hh
  exact hh.symm
noncomputable def bY (D:ℝ):Finset GaussianInt :=
  (o8 0 D).toFinset
@[simp] theorem lZ (D:ℝ) (z:GaussianInt) :
    z ∈ bY D ↔ ‖(z:ℂ)‖ ≤ D:=by simp [bY]
theorem Dv {a b:GaussianInt} (h:a.re*b.im-a.im*b.re ≠ 0) :
    ((b:ℂ)/(a:ℂ)).im ≠ 0:=by
  have ha:a ≠ 0:=by intro hh; simp [hh] at h
  have hac:(a:ℂ) ≠ 0:=by simpa using ha
  have hn:Complex.normSq (a:ℂ) ≠ 0:=(Complex.normSq_pos.mpr hac).ne'
  rw [Complex.div_im,← sub_div]
  intro hh
  have hh':=(div_eq_zero_iff.mp hh).resolve_right hn
  have hz:(a.re:ℝ)*(b.im:ℝ)-(a.im:ℝ)*(b.re:ℝ) = 0:=by
    simpa only [← GaussianInt.intCast_re,← GaussianInt.intCast_im,mul_comm] using hh'
  apply h
  exact_mod_cast hz
theorem tj (v u:ℕ → GaussianInt) {n m:ℕ}
    (hn:0 < n) (hm:0 < m) (a b:GaussianInt)
    (hv0:v 0 = 0) (hu0:u 0 = 0) (hvn:v n = a) (hum:u m = b)
    (hab:a.re*b.im-a.im*b.re ≠ 0) {D:ℝ} (hD:0 ≤ D)
    (hv:∀ i < n,dist (v i:ℂ) (v (i+1):ℂ) ≤ D)
    (hu:∀ j < m,dist (u j:ℂ) (u (j+1):ℂ) ≤ D) (w:GaussianInt) :
    ∃ i < n,∃ j < m,∃ s t:ℤ,
      ‖((v i-u j+(s:GaussianInt)*a+(t:GaussianInt)*b-w:GaussianInt):ℂ)‖ ≤ 4*D:=by
  have ha:a ≠ 0:=by intro hh; simp [hh] at hab
  obtain ⟨i,hi,j,hj,s,t,hh⟩:=s9
    (fun i=>(v i:ℂ)) (fun j=>(u j:ℂ)) hn hm (a:ℂ) (b:ℂ)
    (by simp [hv0]) (by simp [hu0]) (by simp [hvn]) (by simp [hum])
    (by simpa using ha) (Dv hab) hD hv hu (w:ℂ)
  exact ⟨i,hi,j,hj,s,t,by simpa using hh⟩
theorem uY (v u:ℕ → GaussianInt) {n m:ℕ}
    (hn:0 < n) (hm:0 < m) (a b:GaussianInt)
    (hv0:v 0 = 0) (hu0:u 0 = 0) (hvn:v n = a) (hum:u m = b)
    (hab:a.re*b.im-a.im*b.re ≠ 0) {D:ℝ} (hD:0 ≤ D)
    (hv:∀ i < n,dist (v i:ℂ) (v (i+1):ℂ) ≤ D)
    (hu:∀ j < m,dist (u j:ℂ) (u (j+1):ℂ) ≤ D)
    (E:Finset GaussianInt) (hE:∀ i < n,∀ j < m,v i-u j ∈ E) :
    (a.re*b.im-a.im*b.re).natAbs ≤ E.card*(bY (4*D)).card:=by
  classical
  let Q:=(gT a b).range
  have hcard:Nat.card (GaussianInt ⧸ Q) = (a.re*b.im-a.im*b.re).natAbs :=
    nV hab
  have:Finite (GaussianInt ⧸ Q):=Nat.finite_of_card_ne_zero (by rw [hcard]; simpa using hab)
  let:Fintype (GaussianInt ⧸ Q):=Fintype.ofFinite _
  let F:E × (bY (4*D)) → GaussianInt ⧸ Q :=
    fun x=>Q.mkQ (x.1.val+x.2.val)
  have hf:Function.Surjective F:=by
    intro q
    obtain ⟨w,rfl⟩:=Q.mkQ_surjective q
    obtain ⟨i,hi,j,hj,s,t,hh⟩:=tj v u hn hm a b hv0 hu0 hvn hum hab hD hv hu w
    let r:GaussianInt := -(v i-u j+(s:GaussianInt)*a+(t:GaussianInt)*b-w)
    have hr:r ∈ bY (4*D):=by
      rw [lZ]
      dsimp only [r]
      rw [map_neg,norm_neg]
      exact hh
    refine ⟨(⟨v i-u j,hE i hi j hj⟩,⟨r,hr⟩),?_⟩
    apply (Submodule.Quotient.eq Q).mpr
    change (v i-u j)+r-w ∈ (gT a b).range
    refine ⟨⟨-s,-t⟩,?_⟩
    rw [oI]
    change (-s) • a + (-t) • b = _
    simp only [zsmul_eq_mul,Int.cast_neg]
    dsimp [r]
    ring
  have hh:=Fintype.card_le_of_surjective F hf
  have hQ:Fintype.card (GaussianInt ⧸ Q) = (a.re*b.im-a.im*b.re).natAbs:=by
    rw [← Nat.card_eq_fintype_card,hcard]
  simpa only [Fintype.card_prod,Fintype.card_coe,hQ] using hh
theorem I7 {z:GaussianInt} (hz:z ≠ 0):1 ≤ ‖(z:ℂ)‖:=by
  have hi:1 ≤ z.norm:=by have:=GaussianInt.norm_pos.mpr hz; omega
  have hr:(1:ℝ) ≤ (z.norm:ℝ):=by exact_mod_cast hi
  rw [GaussianInt.intCast_real_norm,Complex.normSq_eq_norm_sq] at hr
  nlinarith [norm_nonneg (z:ℂ)]
theorem tO {z w:GaussianInt} (h:z ≠ w) :
    1 ≤ dist (z:ℂ) (w:ℂ):=by
  simpa only [map_sub,dist_eq_norm] using I7 (sub_ne_zero.mpr h)
noncomputable def Ac (e c:ℂ) (z:GaussianInt):ℤ × ℤ :=
  (⌊2*(e*((z:ℂ)-c)).re⌋,⌊2*(e*((z:ℂ)-c)).im⌋)
theorem nD {x y:ℝ} (h:⌊2*x⌋ = ⌊2*y⌋):|x-y| < 1/2:=by
  have h1:=Int.floor_le (2*x)
  have h2:=Int.lt_floor_add_one (2*x)
  have h3:=Int.floor_le (2*y)
  have h4:=Int.lt_floor_add_one (2*y)
  rw [h] at h1 h2
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
theorem Dw {e:ℂ} (he:‖e‖ = 1) (c:ℂ) :
    Function.Injective (Ac e c):=by
  intro z w h
  have hr:=nD (congrArg Prod.fst h)
  have hi:=nD (congrArg Prod.snd h)
  have hn:‖e*((z:ℂ)-c)-e*((w:ℂ)-c)‖ < 1:=by
    have hh:=Complex.norm_le_abs_re_add_abs_im (e*((z:ℂ)-c)-e*((w:ℂ)-c))
    simp only [Complex.sub_re,Complex.sub_im] at hh
    change |(e*((z:ℂ)-c)).re-(e*((w:ℂ)-c)).re| < 1/2 at hr
    change |(e*((z:ℂ)-c)).im-(e*((w:ℂ)-c)).im| < 1/2 at hi
    linarith
  have heq:e*((z:ℂ)-c)-e*((w:ℂ)-c) = e*((z:ℂ)-(w:ℂ)):=by ring
  rw [heq,norm_mul,he,one_mul] at hn
  by_contra hne
  exact (not_lt_of_ge (tO hne)) (by simpa only [dist_eq_norm] using hn)
theorem qB (E:Finset GaussianInt) {e c:ℂ} (he:‖e‖ = 1)
    {R W:ℝ} (hR:1 ≤ R) (hW:1 ≤ W)
    (hE:∀ z ∈ E,0 ≤ (e*((z:ℂ)-c)).re ∧ (e*((z:ℂ)-c)).re ≤ R ∧
      |(e*((z:ℂ)-c)).im| ≤ W) :
    (E.card:ℝ) ≤ 18*R*W:=by
  classical
  let B:Finset (ℤ × ℤ):=Finset.Icc 0 ⌊2*R⌋ ×ˢ Finset.Icc ⌊-2*W⌋ ⌊2*W⌋
  have hb:E.image (Ac e c) ⊆ B:=by
    intro x hx
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨hz0,hzR,hzW⟩:=hE z hz
    have hzw:=abs_le.mp hzW
    simp only [B,Finset.mem_product,Finset.mem_Icc,Ac]
    refine ⟨⟨?_,Int.floor_mono (by linarith)⟩,
      ⟨Int.floor_mono (by linarith),Int.floor_mono (by linarith)⟩⟩
    exact Int.floor_nonneg.mpr (by linarith)
  have hcard:E.card ≤ B.card:=by
    rw [← Finset.card_image_iff.mpr (Dw he c).injOn]
    exact Finset.card_le_card hb
  have hR0:(0:ℤ) ≤ ⌊2*R⌋+1:=by
    have hh:(0:ℤ) ≤ ⌊2*R⌋:=Int.floor_nonneg.mpr (by linarith)
    omega
  have VK:⌊-2*W⌋ ≤ ⌊2*W⌋+1:=by
    have hh:⌊-2*W⌋ ≤ ⌊2*W⌋:=Int.floor_mono (by linarith)
    omega
  have hcr:((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ) = (⌊2*R⌋:ℝ)+1:=by
    have h:=Int.card_Icc_of_le 0 ⌊2*R⌋ hR0
    simp only [sub_zero] at h
    exact_mod_cast h
  have YC:((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) = (⌊2*W⌋:ℝ)+1-(⌊-2*W⌋:ℝ):=by
    exact_mod_cast Int.card_Icc_of_le ⌊-2*W⌋ ⌊2*W⌋ VK
  have hrb:((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ) ≤ 3*R:=by
    rw [hcr]
    linarith [Int.floor_le (2*R)]
  have hwb:((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ) ≤ 6*W:=by
    rw [YC]
    linarith [Int.floor_le (2*W),Int.lt_floor_add_one (-2*W)]
  have hh:(E.card:ℝ) ≤ ((Finset.Icc (0:ℤ) ⌊2*R⌋).card:ℝ)*
      ((Finset.Icc ⌊-2*W⌋ ⌊2*W⌋).card:ℝ):=by
    dsimp only [B] at hcard
    rw [Finset.card_product] at hcard
    exact_mod_cast hcard
  calc
    (E.card:ℝ) ≤ _:=hh
    _ ≤ (3*R)*(6*W):=mul_le_mul hrb hwb (Nat.cast_nonneg _) (by linarith)
    _ = 18*R*W:=by ring
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
noncomputable def dK (z:ℕ → GaussianInt) (n:ℕ):Finset GaussianInt :=
  (Finset.range (n+1)).image z
noncomputable def differences (E:Finset GaussianInt):Finset GaussianInt :=
  (E ×ˢ E).image (fun p=>p.1-p.2)
@[simp] theorem j9 (z:ℕ → GaussianInt) (n:ℕ) (w:GaussianInt) :
    w ∈ dK z n ↔ ∃ i ≤ n,z i = w:=by
  simp [dK,Finset.mem_image]
@[simp] theorem kQ (E:Finset GaussianInt) (w:GaussianInt) :
    w ∈ differences E ↔ ∃ a ∈ E,∃ b ∈ E,a-b = w:=by
  simp [differences,Finset.mem_image,Prod.exists,and_assoc]
theorem Ak {E:Finset GaussianInt} (hE:E.Nonempty) :
    E.card ≤ (differences E).card:=by
  classical
  obtain ⟨a,ha⟩:=hE
  have hs:E.image (fun b=>b-a) ⊆ differences E:=by
    intro w hw
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hw
    exact kQ E (b-a) |>.mpr ⟨b,hb,a,ha,rfl⟩
  have hi:Function.Injective (fun b:GaussianInt=>b-a):=sub_left_injective
  rw [← Finset.card_image_of_injective E hi]
  exact Finset.card_le_card hs
theorem tP (z:ℕ → GaussianInt) {n:ℕ} {D:ℝ} (hD:0 ≤ D)
    (hz:∀ i < n,dist (z i:ℂ) (z (i+1):ℂ) ≤ D) {i j:ℕ} (hi:i ≤ n) (hj:j ≤ n) :
    dist (z i:ℂ) (z j:ℂ) ≤ D*n:=by
  wlog hij:i ≤ j generalizing i j
  · rw [dist_comm]
    exact this hj hi (by omega)
  have h:=dist_le_Ico_sum_of_dist_le (f:=fun k=>(z k:ℂ)) hij
    (d:=fun _=>D) (fun {k} _ hk=>hz k (lt_of_lt_of_le hk hj))
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at h
  calc
    dist (z i:ℂ) (z j:ℂ) ≤ (j-i:ℕ)*D:=h
    _ ≤ (n:ℝ)*D:=mul_le_mul_of_nonneg_right (by exact_mod_cast (show j-i ≤ n by omega)) hD
    _ = D*n:=mul_comm _ _
def kM (z:ℕ → GaussianInt) (t:ℕ) (i:ℕ):GaussianInt :=
  z (Nat.dist t i)-z t
@[simp] theorem C5 (z:ℕ → GaussianInt) (t:ℕ):kM z t 0 = 0:=by
  simp [kM,Nat.dist]
@[simp] theorem Er (z:ℕ → GaussianInt) (t s:ℕ) :
    kM z t (t+s) = z s-z t:=by simp [kM,Nat.dist]
theorem C7 (z:ℕ → GaussianInt) {n t s:ℕ} (ht:t ≤ n) (hs:s ≤ n)
    {D:ℝ} (hz:∀ i < n,dist (z i:ℂ) (z (i+1):ℂ) ≤ D) :
    ∀ i < t+s,dist (kM z t i:ℂ) (kM z t (i+1):ℂ) ≤ D:=by
  intro i hi
  simp only [kM,map_sub,dist_sub_right]
  by_cases hit:i < t
  · have he:Nat.dist t i = Nat.dist t (i+1)+1:=by simp only [Nat.dist]; omega
    rw [he,dist_comm]
    exact hz _ (by simp only [Nat.dist]; omega)
  · have he:Nat.dist t (i+1) = Nat.dist t i+1:=by simp only [Nat.dist]; omega
    rw [he]
    exact hz _ (by simp only [Nat.dist]; omega)
theorem uZ (z:ℕ → GaussianInt) {n t s u:ℕ}
    (ht:t ≤ n) (hs:s ≤ n) (hu:u ≤ n) {D:ℝ} (hD:0 ≤ D)
    (hz:∀ i < n,dist (z i:ℂ) (z (i+1):ℂ) ≤ D)
    (hab:(z s-z t).re*(z u-z t).im-(z s-z t).im*(z u-z t).re ≠ 0) :
    ((z s-z t).re*(z u-z t).im-(z s-z t).im*(z u-z t).re).natAbs ≤
      (differences (dK z n)).card * (bY (4*D)).card:=by
  have hts:0 < t+s:=by
    by_contra hh
    have ht0:t=0:=by omega
    have hs0:s=0:=by omega
    simp [ht0,hs0] at hab
  have htu:0 < t+u:=by
    by_contra hh
    have ht0:t=0:=by omega
    have hu0:u=0:=by omega
    simp [ht0,hu0] at hab
  apply uY (kM z t) (kM z t) hts htu
    (z s-z t) (z u-z t) (C5 z t) (C5 z t)
    (Er z t s) (Er z t u) hab hD
    (C7 z ht hs hz) (C7 z ht hu hz)
  intro i hi j hj
  apply (kQ _ _).mpr
  refine ⟨z (Nat.dist t i),(j9 _ _ _).mpr ⟨_,?_,rfl⟩,
    z (Nat.dist t j),(j9 _ _ _).mpr ⟨_,?_,rfl⟩,?_⟩
  · simp only [Nat.dist]; omega
  · simp only [Nat.dist]; omega
  · simp only [kM]; ring
noncomputable def f8 (a:ℂ):ℂ:=star a / (‖a‖:ℂ)
theorem mL {a:ℂ} (ha:a ≠ 0):‖f8 a‖ = 1:=by
  simp [f8,Complex.norm_real,norm_ne_zero_iff.mpr ha]
theorem F6 (a:ℂ):f8 a*a = (‖a‖:ℂ):=by
  by_cases ha:a=0
  · simp [ha,f8]
  have hn:(‖a‖:ℂ) ≠ 0:=by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hm:star a*a = (‖a‖:ℂ)^2:=Complex.conj_mul' a
  rw [f8,div_mul_eq_mul_div,hm]
  field_simp
theorem JO {a v:ℂ} (ha:a ≠ 0) (hv:‖v‖ ≤ ‖a‖)
    (hva:‖v-a‖ ≤ ‖a‖) :
    0 ≤ (f8 a*v).re ∧ (f8 a*v).re ≤ ‖a‖ ∧
      |(f8 a*v).im| ≤ ‖a‖:=by
  let u:=f8 a*v
  have hn:‖u‖ ≤ ‖a‖:=by simpa [u,norm_mul,mL ha] using hv
  have hna:‖u-(‖a‖:ℂ)‖ ≤ ‖a‖:=by
    rw [← F6 a,← mul_sub]
    simpa [norm_mul,mL ha] using hva
  have hr:=Complex.abs_re_le_norm u
  have hi:=Complex.abs_im_le_norm u
  have hra:=Complex.abs_re_le_norm (u-(‖a‖:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hra
  have hl:=(abs_le.mp (hra.trans hna)).1
  exact ⟨by dsimp [u] at *; linarith,(le_abs_self u.re).trans (hr.trans hn),hi.trans hn⟩
theorem Nu (a b:GaussianInt) :
    |((a.re*b.im-a.im*b.re:ℤ):ℝ)| =
      ‖(a:ℂ)‖*|(f8 (a:ℂ)*(b:ℂ)).im|:=by
  by_cases ha:a=0
  · simp [ha,f8]
  have hna:‖(a:ℂ)‖ ≠ 0:=norm_ne_zero_iff.mpr (by simpa using ha)
  have he:(f8 (a:ℂ)*(b:ℂ)).im =
      ((a.re:ℝ)*(b.im:ℝ)-(a.im:ℝ)*(b.re:ℝ))/‖(a:ℂ)‖:=by
    simp only [f8,div_mul_eq_mul_div,Complex.div_ofReal_im,
      Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      ← GaussianInt.intCast_re,← GaussianInt.intCast_im]
    ring
  rw [he,abs_div,abs_of_nonneg (norm_nonneg (a:ℂ))]
  push_cast
  field_simp
theorem Et (z:ℕ → GaussianInt) {n:ℕ} (hn:1 ≤ n)
    (hinj:Function.Injective z) {D:ℝ} (hD:1 ≤ D)
    (hz:∀ i < n,dist (z i:ℂ) (z (i+1):ℂ) ≤ D) :
    ∃ (R W:ℝ) (e c:ℂ),1 ≤ W ∧ W ≤ R ∧ ‖e‖ = 1 ∧
      (∀ p ∈ dK z n,0 ≤ (e*((p:ℂ)-c)).re ∧
        (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W) ∧
      (n:ℝ) ≤ 18*(R*W) ∧ R*W ≤ D^2*(n:ℝ)^2 ∧
      R*W ≤ max D ((bY (4*D)).card:ℝ)*(differences (dK z n)).card:=by
  classical
  let I:=Finset.range (n+1)
  have hI:I.Nonempty:=⟨0,by simp [I]⟩
  obtain ⟨⟨t,s⟩,hts,hmax⟩:=Finset.exists_max_image (I ×ˢ I)
    (fun q=>dist (z q.1:ℂ) (z q.2:ℂ)) (hI.product hI)
  have ht:t ≤ n:=by simpa [I] using (Finset.mem_product.mp hts).1
  have hs:s ≤ n:=by simpa [I] using (Finset.mem_product.mp hts).2
  let a:=z s-z t
  let R:=‖(a:ℂ)‖
  have hdiam:∀ i ≤ n,∀ j ≤ n,dist (z i:ℂ) (z j:ℂ) ≤ R:=by
    intro i hi j hj
    have h:=hmax (i,j) (by simp [I,hi,hj])
    simpa [R,a,map_sub,← dist_eq_norm,dist_comm] using h
  have hR:1 ≤ R:=(tO (hinj.ne (by omega:0 ≠ 1))).trans (hdiam 0 (by omega) 1 hn)
  have ha:a ≠ 0:=by intro hh; simp [R,hh] at hR; linarith
  have hac:(a:ℂ) ≠ 0:=by simpa using ha
  let e:=f8 (a:ℂ)
  let c:=(z t:ℂ)
  have he:‖e‖ = 1:=mL hac
  have hr:∀ i ≤ n,0 ≤ (e*((z i:ℂ)-c)).re ∧
      (e*((z i:ℂ)-c)).re ≤ R ∧ |(e*((z i:ℂ)-c)).im| ≤ R:=by
    intro i hi
    have hv:‖(z i:ℂ)-c‖ ≤ ‖(a:ℂ)‖:=by simpa only [← dist_eq_norm] using hdiam i hi t ht
    have hva:‖((z i:ℂ)-c)-(a:ℂ)‖ ≤ ‖(a:ℂ)‖:=by
      have hh:((z i:ℂ)-c)-(a:ℂ) = (z i:ℂ)-(z s:ℂ):=by simp [a,c]
      rw [hh,← dist_eq_norm]
      exact hdiam i hi s hs
    exact JO hac hv hva
  obtain ⟨u,hu,WQ⟩:=Finset.exists_max_image I
    (fun i=>|(e*((z i:ℂ)-c)).im|) hI
  have hu':u ≤ n:=by simpa [I] using hu
  let W:=max 1 |(e*((z u:ℂ)-c)).im|
  have hW:1 ≤ W:=le_max_left _ _
  have q8:W ≤ R:=max_le hR (hr u hu').2.2
  have Qj:∀ p ∈ dK z n,0 ≤ (e*((p:ℂ)-c)).re ∧
      (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W:=by
    intro p hp
    obtain ⟨i,hi,rfl⟩:=(j9 _ _ _).mp hp
    exact ⟨(hr i hi).1,(hr i hi).2.1,(WQ i (by simpa [I] using hi)).trans (le_max_right _ _)⟩
  have hcard:(dK z n).card = n+1:=by
    rw [dK,Finset.card_image_of_injective _ hinj,Finset.card_range]
  have hcount:(n:ℝ)+1 ≤ 18*R*W:=by
    have h:=qB (dK z n) he hR hW Qj
    simpa only [hcard,Nat.cast_add,Nat.cast_one] using h
  have VN:R ≤ D*n:=by
    simpa only [R,a,map_sub,← dist_eq_norm] using tP z (by linarith) hz hs ht
  have U6:R*W ≤ D^2*(n:ℝ)^2:=by
    have hn0:(0:ℝ) ≤ n:=Nat.cast_nonneg _
    have hm:=mul_le_mul VN VN (by linarith:0 ≤ R) (by positivity:0 ≤ D*n)
    have hw:=mul_le_mul_of_nonneg_left q8 (by linarith:0 ≤ R)
    nlinarith
  refine ⟨R,W,e,c,hW,q8,he,Qj,by nlinarith,U6,?_⟩
  have VO:=Ak (E:=dK z n)
    ⟨z 0,(j9 _ _ _).mpr ⟨0,by omega,rfl⟩⟩
  have Xw:(n:ℝ)+1 ≤ ((differences (dK z n)).card:ℝ):=by
    rw [hcard] at VO
    exact_mod_cast VO
  by_cases WR:|(e*((z u:ℂ)-c)).im| ≤ 1
  · have Tz:W = 1:=max_eq_left WR
    rw [Tz,mul_one]
    have hdn:D*(n:ℝ) ≤ D*((differences (dK z n)).card:ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact (VN.trans hdn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have Tz:W = |(e*((z u:ℂ)-c)).im|:=max_eq_right (by linarith)
    let b:=z u-z t
    have hdet:|((a.re*b.im-a.im*b.re:ℤ):ℝ)| = R*W:=by
      rw [Nu,Tz]
      simp only [R,e,b,map_sub,c]
    have hab:a.re*b.im-a.im*b.re ≠ 0:=by
      intro hh
      rw [hh,Int.cast_zero,abs_zero] at hdet
      have:0 < R*W:=mul_pos (by linarith) (by linarith)
      linarith
    have hcd:=uZ z ht hs hu' (by linarith) hz hab
    have VT:|((a.re*b.im-a.im*b.re:ℤ):ℝ)| ≤
        ((differences (dK z n)).card:ℝ)*((bY (4*D)).card:ℝ):=by
      have hh:((a.re*b.im-a.im*b.re).natAbs:ℝ) ≤
          ((differences (dK z n)).card:ℝ)*((bY (4*D)).card:ℝ):=by
        exact_mod_cast hcd
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
    rw [hdet] at VT
    calc
      R*W ≤ ((differences (dK z n)).card:ℝ)*((bY (4*D)).card:ℝ):=VT
      _ = ((bY (4*D)).card:ℝ)*((differences (dK z n)).card:ℝ):=mul_comm _ _
      _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD dD g4 c9 oG Mc RO
namespace GaussianMoat
namespace aD
section
variable {Ω:Type bU} [Fintype Ω]
noncomputable def Hf {α:Type cD} (p:aD Ω) (X:Ω → α):ℝ:=by
  classical
  exact -∑ ω,p ω * Real.log (∑ ν,if X ν = X ω then p ν else 0)
noncomputable def bT {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β):ℝ :=
  p.Hf (fun ω=>(X ω,Y ω))-p.Hf Y
theorem jW {α:Type cD} [Fintype α] (p:aD Ω) (X:Ω → α):p.Hf X = p.H X:=by
  classical
  rw [F5]
  simp only [Hf,f7]
theorem aZ {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (hf:∀ ω ν,X ω = X ν ↔ Y ω = Y ν):p.Hf X = p.Hf Y:=by
  classical
  unfold Hf
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  congr 2
  apply Finset.sum_congr rfl
  intro ν _
  rw [hf]
noncomputable def LD {α:Type cD} (X:Ω → α):Finset α:=by
  classical
  exact Finset.univ.image X
noncomputable def ju {α:Type cD} (X:Ω → α) (ω:Ω):LD X :=
  ⟨X ω,by
    classical
    simp [LD]⟩
@[simp] theorem gO {α:Type cD} (X:Ω → α) (ω ν:Ω) :
    ju X ω = ju X ν ↔ X ω = X ν:=Subtype.ext_iff
theorem u6 {α:Type cD} (p:aD Ω) (X:Ω → α) :
    p.Hf X = p.H (ju X):=by
  rw [← jW]
  exact p.aZ _ _ (fun _ _=>(gO _ _ _).symm)
theorem r6 {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.Hf (fun ω=>(X ω,Y ω)) = p.H (fun ω=>(ju X ω,ju Y ω)):=by
  rw [← jW]
  apply p.aZ
  simp only [Prod.mk.injEq,gO,implies_true]
theorem Ox {α:Type cD} {β:Type dD} {γ:Type g4} (p:aD Ω)
    (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.Hf (fun ω=>(X ω,(Y ω,Z ω))) =
      p.H (fun ω=>(ju X ω,(ju Y ω,ju Z ω))):=by
  rw [← jW]
  apply p.aZ
  simp only [Prod.mk.injEq,gO,implies_true]
theorem JQ {α:Type cD} (p:aD Ω) (X:Ω → α):0 ≤ p.Hf X:=by
  rw [u6]
  exact (p.map _).Om
theorem Ry {α:Type cD} (p:aD Ω) (X:Ω → α) :
    p.Hf X ≤ Real.log (Fintype.card Ω):=by
  rw [u6]
  refine (p.map _).lK.trans ?_
  have XO:=Fintype.card_le_of_surjective (ju X) (fun ⟨x,hx⟩=>by
    classical
    obtain ⟨ω,_,hω⟩:=Finset.mem_image.mp hx
    exact ⟨ω,Subtype.ext hω⟩)
  exact Real.log_le_log (by exact_mod_cast Fintype.card_pos_iff.mpr (p.map (ju X)).nonempty)
    (by exact_mod_cast XO)
theorem kd {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.Hf (fun ω=>(X ω,Y ω)) = p.Hf (fun ω=>(Y ω,X ω)):=by
  apply p.aZ
  simp only [Prod.mk.injEq,and_comm,implies_true]
theorem Pk {α:Type cD} {β:Type dD} {γ:Type g4} (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.Hf (fun ω=>(X ω,(Y ω,Z ω))) = p.Hf (fun ω=>((X ω,Y ω),Z ω)):=by
  apply p.aZ
  simp only [Prod.mk.injEq,and_assoc,implies_true]
theorem kH {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.Hf Y ≤ p.Hf (fun ω=>(X ω,Y ω)):=by
  rw [r6,u6]
  exact p.qL _ _
theorem kJ {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.Hf (fun ω=>(X ω,Y ω)) ≤ p.Hf X+p.Hf Y:=by
  rw [r6,u6 p X,u6 p Y]
  exact p.wR _ _
theorem Md {α:Type cD} {β:Type dD} {γ:Type g4} (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.Hf (fun ω=>(X ω,(Y ω,Z ω)))+p.Hf Y ≤
      p.Hf (fun ω=>(X ω,Y ω))+p.Hf (fun ω=>(Y ω,Z ω)):=by
  rw [Ox,u6 p Y,r6 p X Y,r6 p Y Z]
  exact p.CY _ _ _
theorem F7 {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    0 ≤ p.bT X Y:=sub_nonneg.mpr (p.kH X Y)
theorem C8 {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.bT X Y ≤ p.Hf X:=by have:=p.kJ X Y; unfold bT; linarith
theorem u7 {α:Type cD} {β:Type dD} {γ:Type g4} (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.bT X (fun ω=>(Y ω,Z ω)) ≤ p.bT X Y:=by
  have:=p.Md X Y Z
  unfold bT
  linarith
theorem WS {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (f:α → β) :
    p.Hf (f ∘ X) ≤ p.Hf X:=by
  have h:=p.kH X (f ∘ X)
  have he:p.Hf (fun ω=>(X ω,(f ∘ X) ω)) = p.Hf X :=
    p.aZ _ _ (fun _ _=>by
      simp only [Prod.mk.injEq,Function.comp_def]
      exact ⟨And.left,fun hh=>⟨hh,congrArg f hh⟩⟩)
  rwa [he] at h
theorem lN {α:Type cD} {β:Type dD} (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (h:∀ ω ν,Y ω = Y ν → X ω = X ν):p.Hf X ≤ p.Hf Y:=by
  have hh:=p.kH Y X
  have he:p.Hf (fun ω=>(Y ω,X ω)) = p.Hf Y :=
    p.aZ _ _ (fun ω ν=>by
      simp only [Prod.mk.injEq]
      exact ⟨And.left,fun hh=>⟨hh,h ω ν hh⟩⟩)
  rwa [he] at hh
theorem Ao {α:Type cD} (p:aD Ω) (a:α):p.Hf (fun _=>a) = 0:=by
  classical
  simp [Hf,p.dN]
theorem Me {ι:Type c9} {α:Type cD} (p:aD Ω) (X:Ω → ι → α) (S:Finset ι) :
    p.Hf (fun ω (i:S)=>X ω i) ≤ ∑ i ∈ S,p.Hf (fun ω=>X ω i):=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he:p.Hf (fun ω (i:(∅:Finset ι))=>X ω i) = p.Hf (fun _=>()):=by
      apply p.aZ
      intro ω ν
      simp only [iff_true]
      funext i
      exact False.elim (Finset.notMem_empty i.val i.property)
    simp [he,p.Ao]
  | @insert i S hi ih =>
    have he:p.Hf (fun ω (j:(insert i S:Finset ι))=>X ω j) =
        p.Hf (fun ω=>(X ω i,fun j:S=>X ω j)):=by
      apply p.aZ
      intro ω ν
      constructor
      · intro h
        apply Prod.ext
        · exact congrFun h ⟨i,Finset.mem_insert_self _ _⟩
        · funext j; exact congrFun h ⟨j,Finset.mem_insert_of_mem j.property⟩
      · intro h
        funext j
        rcases Finset.mem_insert.mp j.property with hj | hj
        · simpa [hj] using congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) ⟨j,hj⟩
    rw [he,Finset.sum_insert hi]
    have hh:=p.kJ (fun ω=>X ω i) (fun ω (j:S)=>X ω j)
    linarith
end
open scoped BigOperators
variable {Ω:Type bU} {α:Type cD} [Fintype Ω] {k:ℕ}
def aF (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k)) (s:ℕ) (ω:Ω) (i:Fin k):Option α :=
  if i.val < s then some (X ω (π i)) else none
noncomputable def bF (p:aD Ω) (X:Ω → Fin k → α) (s:ℕ):ℝ :=
  𝔼 π:Equiv.Perm (Fin k),p.Hf (aF X π s)
omit [Fintype Ω] in
@[simp] theorem Oy (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k)) (ω:Ω) :
    aF X π 0 ω = fun _=>none:=by funext i; simp [aF]
@[simp] theorem Sj (p:aD Ω) (X:Ω → Fin k → α) :
    p.bF X 0 = 0:=by
  have h (π:Equiv.Perm (Fin k)):aF X π 0 = fun _ _=>none:=by
    funext ω i
    simp [aF]
  simp [bF,h,Finset.expect,p.Ao]
theorem Ew (p:aD Ω) (X:Ω → Fin k → α) (s:ℕ) :
    0 ≤ p.bF X s:=Finset.expect_nonneg (fun _ _=>p.JQ _)
theorem Nv (p:aD Ω) (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k))
    {s:ℕ} (hs:s < k) :
    p.Hf (aF X π (s+1)) =
      p.Hf (fun ω=>(X ω (π ⟨s,hs⟩),aF X π s ω)):=by
  apply p.aZ
  intro ω ν
  constructor
  · intro h
    apply Prod.ext
    · have hh:=congrFun h ⟨s,hs⟩
      simpa [aF] using hh
    · funext i
      by_cases hi:i.val < s
      · have hh:=congrFun h i
        simpa [aF,hi,show i.val<s+1 by omega] using hh
      · simp [aF,hi]
  · intro h
    funext i
    by_cases hi:i.val < s
    · have hh:=congrFun (congrArg Prod.snd h) i
      simpa [aF,hi,show i.val<s+1 by omega] using hh
    · by_cases his:i.val = s
      · have hieq:i = ⟨s,hs⟩:=Fin.ext his
        subst i
        simpa [aF] using congrArg some (congrArg Prod.fst h)
      · simp [aF,show ¬i.val<s+1 by omega]
theorem lO (p:aD Ω) (X:Ω → Fin k → α) {s:ℕ} (hs:s < k) :
    p.bF X (s+1)-p.bF X s =
      𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π ⟨s,hs⟩)) (aF X π s):=by
  simp only [bF,← Finset.expect_sub_distrib,bT,p.Nv X _ hs]
theorem wT (p:aD Ω) (X:Ω → Fin k → α) (s:ℕ)
    (i j:Fin k) (hi:s ≤ i.val) (hj:s ≤ j.val) :
    (𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π i)) (aF X π s)) =
      𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π j)) (aF X π s):=by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  have hp:aF X (π*Equiv.swap i j) s = aF X π s:=by
    funext ω a
    by_cases ha:a.val<s
    · have hai:a≠i:=by intro he; subst a; omega
      have haj:a≠j:=by intro he; subst a; omega
      simp [aF,ha,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hai haj]
    · simp [aF,ha]
  change p.bT (fun ω=>X ω (π i)) (aF X π s) =
    p.bT (fun ω=>X ω ((π * Equiv.swap i j) j)) (aF X (π * Equiv.swap i j) s)
  rw [hp]
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]
theorem jL {β:Type dD} {γ:Type g4} (p:aD Ω)
    (X:Ω → α) (Y:Ω → β) (Z:Ω → γ)
    (h:∀ ω ν,Y ω = Y ν → Z ω = Z ν):p.bT X Y ≤ p.bT X Z:=by
  have hc:=p.u7 X Z Y
  have hy:p.Hf (fun ω=>(Z ω,Y ω)) = p.Hf Y:=by
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hh=>⟨h ω ν hh,hh⟩⟩
  have hx:p.Hf (fun ω=>(X ω,(Z ω,Y ω))) = p.Hf (fun ω=>(X ω,Y ω)):=by
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨fun hh=>⟨hh.1,hh.2.2⟩,fun hh=>⟨hh.1,h ω ν hh.2,hh.2⟩⟩
  unfold bT at hc ⊢
  rwa [hy,hx] at hc
theorem Dx (p:aD Ω) (X:Ω → Fin k → α) {s:ℕ} (hs:s+1 < k) :
    p.bF X (s+2)-p.bF X (s+1) ≤
      p.bF X (s+1)-p.bF X s:=by
  rw [p.lO X hs,p.lO X (by omega:s<k)]
  rw [p.wT X s ⟨s,by omega⟩ ⟨s+1,hs⟩ (by exact le_rfl) (by exact Nat.le_succ s)]
  apply Finset.expect_le_expect
  intro π _
  apply p.jL
  intro ω ν hh
  funext a
  by_cases ha:a.val < s
  · simpa [aF,ha,show a.val < s+1 by omega] using congrFun hh a
  · simp [aF,ha]
theorem nP (p:aD Ω) (X:Ω → Fin k → α)
    {b:ℕ} (hb:0 < b) (hbk:b < k) :
    p.bF X (b+1)-p.bF X b ≤ p.bF X b / b:=by
  have h (s:ℕ) (hs:s < k) :
      (s:ℝ)*(p.bF X (s+1)-p.bF X s) ≤ p.bF X s:=by
    induction s with
    | zero=>simp
    | succ s ih =>
      have ih':=ih (by omega)
      have hc:=p.Dx X hs
      have hn:(0:ℝ) ≤ s+1:=by positivity
      have hm:=mul_le_mul_of_nonneg_left hc hn
      simp only [Nat.cast_add,Nat.cast_one] at *
      nlinarith
  exact (le_div_iff₀ (by exact_mod_cast hb)).mpr (by nlinarith [h b hbk])
noncomputable def gP (p:aD Ω) (X:(Fin k → Bool) → Ω → Fin k → α) (s:ℕ):ℝ :=
  𝔼 σ:Fin k → Bool,p.bF (X σ) s
@[simp] theorem SN (p:aD Ω) (X:(Fin k → Bool) → Ω → Fin k → α) :
    p.gP X 0 = 0:=by simp [gP,Finset.expect]
theorem Sl (p:aD Ω) (X:(Fin k → Bool) → Ω → Fin k → α)
    {b:ℕ} (hb:0 < b) (hbk:b < k) :
    p.gP X (b+1)-p.gP X b ≤ p.gP X b / b:=by
  unfold gP
  rw [← Finset.expect_sub_distrib,Finset.expect_div]
  exact Finset.expect_le_expect (fun σ _=>p.nP (X σ) hb hbk)
theorem vT {β:Type dD} {γ:Type g4} (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.bT (fun ω=>(X ω,Y ω)) Z = p.bT X Z + p.bT Y (fun ω=>(X ω,Z ω)):=by
  unfold bT
  have he:p.Hf (fun ω=>((X ω,Y ω),Z ω)) = p.Hf (fun ω=>(Y ω,(X ω,Z ω))):=by
    apply p.aZ
    simp only [Prod.mk.injEq]
    tauto
  rw [he]
  ring
theorem C9 {β:Type dD} {γ:Type g4} (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → γ) :
    p.bT (fun ω=>(X ω,Y ω)) Z ≤ p.bT X Z + p.bT Y Z:=by
  rw [p.vT]
  apply add_le_add le_rfl
  apply p.jL
  intro ω ν h
  exact congrArg Prod.snd h
theorem Mh {β:Type dD} {γ:Type g4} {δ:Type oG} {ε:Type Mc} {ζ:Type RO} (p:aD Ω)
    (X:Ω → α) (Y:Ω → β) (Bx:Ω → γ) (By:Ω → δ) (h:Ω → ε) (H:Ω → ζ)
    (hh:∀ ω ν,X ω = X ν → Y ω = Y ν → h ω = h ν)
    (hY:∀ ω ν,X ω = X ν → h ω = h ν → Y ω = Y ν)
    (hH:∀ ω ν,H ω = H ν → h ω = h ν) :
    p.bT h (fun ω=>(Bx ω,By ω)) ≤ p.bT X Bx + p.bT Y By -
      p.bT X (fun ω=>((Bx ω,By ω),H ω)):=by
  let B:=fun ω=>(Bx ω,By ω)
  have he:p.bT (fun ω=>(h ω,X ω)) B = p.bT (fun ω=>(X ω,Y ω)) B:=by
    unfold bT
    congr 1
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨fun ha=>⟨⟨ha.1.2,hY ω ν ha.1.2 ha.1.1⟩,ha.2⟩,
      fun ha=>⟨⟨hh ω ν ha.1.1 ha.1.2,ha.1.1⟩,ha.2⟩⟩
  have hx:p.bT X B ≤ p.bT X Bx :=
    p.jL _ _ _ (fun _ _ he=>congrArg Prod.fst he)
  have hy:p.bT Y B ≤ p.bT Y By :=
    p.jL _ _ _ (fun _ _ he=>congrArg Prod.snd he)
  have ht:p.bT X (fun ω=>(B ω,H ω)) ≤ p.bT X (fun ω=>(h ω,B ω)):=by
    apply p.jL
    intro ω ν he
    apply Prod.ext
    · exact hH ω ν (congrArg Prod.snd he)
    · exact congrArg Prod.fst he
  have hc:=p.vT h X B
  have hs:=p.C9 X Y B
  change p.bT h B ≤ p.bT X Bx + p.bT Y By - p.bT X (fun ω=>(B ω,H ω))
  linarith
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
noncomputable def multiples (π:GaussianInt):Submodule ℤ GaussianInt :=
  (gT π (π * ⟨0,1⟩)).range
lemma JR (π z:GaussianInt) :
    gT π (π * ⟨0,1⟩) z = π*z:=by
  rw [oI]
  ext <;> simp [zsmul_eq_mul,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring
lemma mem_multiples (π z:GaussianInt):z ∈ multiples π ↔ π ∣ z:=by
  simp only [multiples,LinearMap.mem_range,JR]
  exact ⟨fun ⟨a,ha⟩=>⟨a,ha.symm⟩,fun ⟨a,ha⟩=>⟨a,ha.symm⟩⟩
lemma l5 {π:GaussianInt} (hπ:π ≠ 0) :
    Nat.card (GaussianInt ⧸ multiples π) = π.norm.natAbs:=by
  have he:π.re*(π*⟨0,1⟩).im-π.im*(π*⟨0,1⟩).re = π.norm:=by
    simp [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.norm]
  have hn:π.norm ≠ 0:=(GaussianInt.norm_pos.mpr hπ).ne'
  have h:=nV (a:=π) (b:=π*⟨0,1⟩) (he.trans_ne hn)
  simpa only [multiples,he] using h
noncomputable def aY (π z:GaussianInt):GaussianInt ⧸ multiples π :=
  Submodule.Quotient.mk z
lemma jX (π z w:GaussianInt) :
    aY π z = aY π w ↔ π ∣ z-w:=by
  rw [aY,aY,Submodule.Quotient.eq,mem_multiples]
instance:Countable GaussianInt:=nU.injective.countable
instance (π:GaussianInt):Countable (GaussianInt ⧸ multiples π) :=
  (Submodule.Quotient.mk_surjective (p:=multiples π)).countable
noncomputable def aR (π z:GaussianInt):ℕ:=by
  let:=Encodable.ofCountable (GaussianInt ⧸ multiples π)
  exact Encodable.encode (aY π z)
lemma k9 (π z w:GaussianInt) :
    aR π z = aR π w ↔ π ∣ z-w:=by
  let:=Encodable.ofCountable (GaussianInt ⧸ multiples π)
  change Encodable.encode (aY π z) = Encodable.encode (aY π w) ↔ _
  rw [Encodable.encode_inj,jX]
lemma kR {π x y x' y':GaussianInt}
    (hx:aR π x = aR π x') (hy:aR π y = aR π y') :
    aR π (x-y) = aR π (x'-y'):=by
  rw [k9] at *
  convert dvd_sub hx hy using 1; ring
lemma Da {π x y x' y':GaussianInt}
    (hx:aR π x = aR π x') (hy:aR π y = aR π y') :
    aR π (x+y) = aR π (x'+y'):=by
  rw [k9] at *
  convert dvd_add hx hy using 1; ring
lemma kN {π:GaussianInt} (hπ:π ≠ 0) :
    Finite (GaussianInt ⧸ multiples π):=by
  apply Nat.finite_of_card_ne_zero
  rw [l5 hπ]
  simpa only [Int.natAbs_ne_zero] using (GaussianInt.norm_pos.mpr hπ).ne'
lemma Dz {π:GaussianInt} (hπ:π ≠ 0) :
    (Set.range (aR π)).Finite ∧ (Set.range (aR π)).ncard = π.norm.natAbs:=by
  let:=kN hπ
  let:=Encodable.ofCountable (GaussianInt ⧸ multiples π)
  have hs:Function.Surjective (aY π):=Submodule.Quotient.mk_surjective _
  have hr:Set.range (aR π) = Set.range
      (Encodable.encode:(GaussianInt ⧸ multiples π) → ℕ):=by
    change Set.range (Encodable.encode ∘ aY π) = _
    rw [Set.range_comp,hs.range_eq,Set.image_univ]
  rw [hr]
  refine ⟨Set.finite_range _,?_⟩
  rw [Set.ncard_range_of_injective Encodable.encode_injective,l5 hπ]
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open Filter Topology Finset
namespace dS
open ArithmeticFunction.vonMangoldt Complex
lemma I8 {q:ℕ} [NeZero q] {a:ZMod q} (ha:IsUnit a)
    {x:ℝ} (hx:1 < x) :
    ∑' n,residueClass a n / (n:ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient:ℝ)⁻¹ / (x - 1):=by
  refine ofReal_injective ?_
  simp only [ofReal_tsum,ofReal_div,ofReal_cpow (Nat.cast_nonneg _),ofReal_natCast,
    ofReal_add,ofReal_inv,ofReal_sub,ofReal_one]
  simp_rw [← LFunctionResidueClassAux_real ha hx,
    eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx),sub_add_cancel,
    LSeries,LSeries.term]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · simp only [hn,residueClass_apply_zero,ofReal_zero,zero_div]
  · rfl
theorem F9 {q:ℕ} [NeZero q] {a:ZMod q} (ha:IsUnit a)
    {j:ℝ} (hj:0 < j) :
    Tendsto (fun X:ℝ=>(∑' n,residueClass a n / (n:ℝ) ^ (1+j/X)) / X)
      atTop (𝓝 ((q.totient:ℝ)⁻¹ / j)):=by
  have hinv:Tendsto (fun X:ℝ=>j/X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have harg:Tendsto (fun X:ℝ=>((1+j/X:ℝ):ℂ)) atTop (𝓝 1):=by
    have hr:Tendsto (fun X:ℝ=>1+j/X) atTop (𝓝 1):=by
      simpa using hinv.const_add 1
    simpa only [Function.comp_def,ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hmem:∀ᶠ X:ℝ in atTop,((1+j/X:ℝ):ℂ) ∈ {s:ℂ | 1 ≤ s.re}:=by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    change 1 ≤ 1+j/X
    exact le_add_of_nonneg_right (div_nonneg hj.le hX.le)
  have hc:Tendsto (fun X:ℝ=>(LFunctionResidueClassAux a ((1+j/X:ℝ):ℂ)).re)
      atTop (𝓝 (LFunctionResidueClassAux a 1).re):=by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      ((continuousOn_LFunctionResidueClassAux a 1 (by simp)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨harg,hmem⟩))
  have hz:=hc.div_atTop tendsto_id
  have hl:Tendsto (fun X:ℝ=>(LFunctionResidueClassAux a ((1+j/X:ℝ):ℂ)).re / X +
      (q.totient:ℝ)⁻¹ / j) atTop (𝓝 ((q.totient:ℝ)⁻¹ / j)):=by
    simpa using hz.add_const ((q.totient:ℝ)⁻¹ / j)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [I8 ha (by linarith [div_pos hj hX]:1 < 1+j/X)]
  rw [add_div,add_sub_cancel_left,div_div,div_mul_cancel₀ _ hX.ne']
open intervalIntegral MeasureTheory
noncomputable def jf (m n:ℕ):ℝ:=∫ x in (0:ℝ)..1,x^m*(1-x)^n
lemma Oz (m n:ℕ):0 < jf m n:=by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop:Continuous (fun x:ℝ=>x^m*(1-x)^n)).intervalIntegrable _ _
  · intro x hx
    exact mul_pos (pow_pos hx.1 _) (pow_pos (sub_pos.mpr hx.2) _)
  · norm_num
lemma Db (m n:ℕ) :
    jf (m+1) n = (m+1:ℝ)/(m+n+2)*jf m n:=by
  have hd (x:ℝ):HasDerivAt (fun x:ℝ=>x^(m+1)*(1-x)^(n+1))
      ((m+1:ℝ)*x^m*(1-x)^(n+1) - (n+1:ℝ)*x^(m+1)*(1-x)^n) x:=by
    have h1:HasDerivAt (fun y:ℝ=>y^(m+1)) ((m+1:ℝ)*x^m) x:=by
      simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hasDerivAt_pow (m+1) x
    have h2:HasDerivAt (fun y:ℝ=>(1-y)^(n+1)) (-(n+1:ℝ)*(1-x)^n) x:=by
      simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,id_eq,sub_zero,zero_sub,
        mul_neg_one,neg_mul] using! ((hasDerivAt_id x).const_sub 1).pow (n+1)
    convert! h1.mul h2 using 1; ring
  have hInt:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hd x)
    (by exact (by fun_prop:Continuous (fun x:ℝ =>
      (m+1:ℝ)*x^m*(1-x)^(n+1)-(n+1:ℝ)*x^(m+1)*(1-x)^n)).intervalIntegrable 0 1)
  have hsplit:jf m (n+1)+jf (m+1) n = jf m n:=by
    unfold jf
    rw [← intervalIntegral.integral_add]
    · congr 1
      funext x
      rw [pow_succ,pow_succ]
      ring
    · exact (by fun_prop:Continuous (fun x:ℝ=>x^m*(1-x)^(n+1))).intervalIntegrable _ _
    · exact (by fun_prop:Continuous (fun x:ℝ=>x^(m+1)*(1-x)^n)).intervalIntegrable _ _
  have hi (u v:ℕ):IntervalIntegrable (fun x:ℝ=>x^u*(1-x)^v) volume 0 1 :=
    (by fun_prop:Continuous _).intervalIntegrable _ _
  have hmul (c:ℝ) (u v:ℕ) :
      (∫ x:ℝ in 0..1,c*x^u*(1-x)^v) = c*jf u v:=by
    simp only [mul_assoc,intervalIntegral.integral_const_mul,jf]
  rw [intervalIntegral.integral_sub
    (by simpa only [mul_assoc] using (hi m (n+1)).const_mul (m+1:ℝ))
    (by simpa only [mul_assoc] using (hi (m+1) n).const_mul (n+1:ℝ)),
    hmul,hmul] at hInt
  simp only [one_pow,sub_self,zero_pow (Nat.succ_ne_zero _),mul_zero,zero_mul,sub_zero] at hInt
  have hn:(0:ℝ) < m+n+2:=by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn.ne').mpr
  nlinarith
noncomputable def n5 (m n:ℕ):Polynomial ℝ :=
  Polynomial.X^m*(1-Polynomial.X)^n*
    ((Polynomial.X-Polynomial.C (7/20))*(Polynomial.C (11/30)-Polynomial.X))
lemma Aw (m n:ℕ) (y:ℝ) :
    Polynomial.eval y (n5 m n) = y^m*(1-y)^n*((y-7/20)*(11/30-y)):=by
  simp only [n5,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C]
noncomputable def gN:Polynomial ℝ:=n5 1431 2567
lemma mO (y:ℝ) :
    Polynomial.eval y gN = y^1431*(1-y)^2567*((y-7/20)*(11/30-y)) :=
  Aw 1431 2567 y
lemma lT {y:ℝ} (hy:y ∈ Set.Icc (0:ℝ) 1)
    (hout:y ≤ 7/20 ∨ 11/30 ≤ y):Polynomial.eval y gN ≤ 0:=by
  rw [mO]
  have hp:0 ≤ y^1431*(1-y)^2567:=mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg (sub_nonneg.mpr hy.2) _)
  apply mul_nonpos_of_nonneg_of_nonpos hp
  rcases hout with hl | hr
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hl]) (by linarith only [hl])
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hr]) (by linarith only [hr])
lemma Ga (m n:ℕ) (a b:ℝ) :
    (∫ x:ℝ in 0..1,x^m*(1-x)^n*((x-a)*(b-x))) =
      (a+b)*jf (m+1) n-jf (m+2) n-a*b*jf m n:=by
  have he:(fun x:ℝ=>x^m*(1-x)^n*((x-a)*(b-x))) = fun x =>
      (a+b)*(x^(m+1)*(1-x)^n)-(x^(m+2)*(1-x)^n)-a*b*(x^m*(1-x)^n):=by
    funext x
    simp only [pow_add,pow_one,pow_two]
    ring
  have hi (u v:ℕ):IntervalIntegrable (fun x:ℝ=>x^u*(1-x)^v) volume 0 1 :=
    (by fun_prop:Continuous _).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_sub ((hi (m+1) n).const_mul _ |>.sub (hi (m+2) n))
    ((hi m n).const_mul _),
    intervalIntegral.integral_sub ((hi (m+1) n).const_mul _) (hi (m+2) n),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  rfl
lemma tq:0 < ∫ x:ℝ in 0..1,Polynomial.eval x gN:=by
  simp only [mO]
  rw [Ga]
  change 0 < (7/20+11/30)*jf 1432 2567 - jf 1433 2567 -
    (7/20*(11/30))*jf 1431 2567
  rw [Db 1432 2567,Db 1431 2567]
  norm_num only [Nat.cast_ofNat]
  have hp:=Oz 1431 2567
  nlinarith
lemma yZ (P:Polynomial ℝ) :
    (∫ x:ℝ in 0..1,P.eval x) = ∑ j ∈ P.support,P.coeff j / (j+1:ℝ):=by
  simp_rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,integral_pow,one_pow,
      zero_pow (Nat.succ_ne_zero _),sub_zero,mul_one_div]
  · intro j _
    exact (by fun_prop:Continuous (fun x:ℝ=>P.coeff j*x^j)).intervalIntegrable _ _
theorem rG {q:ℕ} [NeZero q] {a:ZMod q} (ha:IsUnit a)
    (P:Polynomial ℝ) :
    Tendsto (fun X:ℝ=>∑ j ∈ P.support,P.coeff j *
      ((∑' n,residueClass a n / (n:ℝ) ^ (1+(j+1:ℝ)/X)) / X)) atTop
      (𝓝 ((q.totient:ℝ)⁻¹ * (∫ x:ℝ in 0..1,P.eval x))):=by
  have h (j:ℕ):=(F9 ha (show (0:ℝ) < j+1 by positivity)).const_mul (P.coeff j)
  have hs:=tendsto_finsetSum P.support (fun j _=>h j)
  convert hs using 1
  congr 1
  rw [yZ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma Az {q:ℕ} [NeZero q] (a:ZMod q) {x:ℝ} (hx:1 < x) :
    Summable (fun n:ℕ=>residueClass a n / (n:ℝ)^x) :=
  LSeries.summable_real_of_abscissaOfAbsConv_lt
    ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx))
lemma Pq (n j:ℕ) (X:ℝ) (hn:n ≠ 0) :
    (n:ℝ) ^ (-(j+1:ℝ)/X) =
      (Real.exp (-Real.log n / X))^(j+1):=by
  rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn),← Real.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma JT {q:ℕ} [NeZero q] (a:ZMod q) (n j:ℕ) (X:ℝ) :
    residueClass a n / (n:ℝ)^(1+(j+1:ℝ)/X) =
      residueClass a n / n * (Real.exp (-Real.log n/X))^(j+1):=by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · rw [Real.rpow_add (by exact_mod_cast hn),Real.rpow_one,div_mul_eq_div_div,
      div_eq_mul_inv _ ((n:ℝ)^((j+1:ℝ)/X)),← Real.rpow_neg (by positivity),
      show -((j+1:ℝ)/X) = -(j+1:ℝ)/X by ring,Pq n j X (by omega)]
lemma zj {q:ℕ} [NeZero q] (a:ZMod q)
    (P:Polynomial ℝ) {X:ℝ} (hX:0 < X) :
    (∑ j ∈ P.support,P.coeff j *
      (∑' n,residueClass a n / (n:ℝ)^(1+(j+1:ℝ)/X))) =
    ∑' n,residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P:=by
  have hs (j:ℕ):Summable (fun n:ℕ=>residueClass a n /
      (n:ℝ)^(1+(j+1:ℝ)/X)):=Az a (by
    have:0 < (j+1:ℝ)/X:=div_pos (by positivity) hX
    linarith)
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _=>(hs j).mul_left (P.coeff j))]
  apply tsum_congr
  intro n
  simp_rw [JT,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring
lemma vV {q:ℕ} [NeZero q] (a:ZMod q)
    (P:Polynomial ℝ) {X:ℝ} (hX:0 < X) :
    Summable (fun n:ℕ=>residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) P):=by
  have hs (j:ℕ):Summable (fun n:ℕ=>P.coeff j * (residueClass a n /
      (n:ℝ)^(1+(j+1:ℝ)/X))):=(Az a (by
    have:0 < (j+1:ℝ)/X:=div_pos (by positivity) hX
    linarith)).mul_left _
  apply (summable_sum (s:=P.support) (fun j _=>hs j)).congr
  intro n
  simp_rw [JT,Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring
lemma BZ {y:ℝ} (hy:y ∈ Set.Icc (0:ℝ) 1) :
    Polynomial.eval y gN ≤ 1:=by
  by_cases hl:y ≤ 7/20
  · exact (lT hy (.inl hl)).trans (by norm_num)
  by_cases hr:11/30 ≤ y
  · exact (lT hy (.inr hr)).trans (by norm_num)
  rw [mO]
  have h1:0 ≤ y^1431:=pow_nonneg hy.1 _
  have h2:0 ≤ (1-y)^2567:=pow_nonneg (by linarith only [hy.2]) _
  have he:y^1431*(1-y)^2567 ≤ 1 :=
    (mul_le_of_le_one_left h2 (pow_le_one₀ hy.1 hy.2)).trans
      (pow_le_one₀ (by linarith only [hy.2]) (by linarith only [hy.1]))
  have hf:(y-7/20)*(11/30-y) ≤ 1 :=
    (mul_le_of_le_one_left (by linarith only [hr]) (by linarith only [hy.2])).trans
      (by linarith only [hy.1])
  exact (mul_le_of_le_one_left
    (mul_nonneg (by linarith only [hl]) (by linarith only [hr])) he).trans hf
lemma Mj:Real.exp (-(10499/10000:ℝ)) < 7/20:=by
  have h:=Real.quadratic_le_exp_of_nonneg (by norm_num:(0:ℝ) ≤ 499/10000)
  have he:=Real.exp_one_gt_d9
  have hp:Real.exp (10499/10000:ℝ) = Real.exp 1 * Real.exp (499/10000:ℝ):=by
    rw [← Real.exp_add]
    norm_num
  rw [Real.exp_neg,hp]
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith
lemma Ml:(11/30:ℝ) < Real.exp (-(1001/1000:ℝ)):=by
  have h:=Real.exp_bound_div_one_sub_of_interval (by norm_num:(0:ℝ) ≤ 1/1000)
    (by norm_num:(1/1000:ℝ) < 1)
  have hp:Real.exp (1001/1000:ℝ) = Real.exp 1 * Real.exp (1/1000:ℝ):=by
    rw [← Real.exp_add]
    norm_num
  rw [Real.exp_neg,inv_eq_one_div]
  apply (lt_div_iff₀ (Real.exp_pos _)).mpr
  rw [hp]
  have hm:=mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le
  norm_num at hm
  nlinarith [Real.exp_one_lt_d9]
noncomputable def f5 (X:ℝ):Finset ℕ:=by
  classical
  exact (Finset.range (⌊Real.exp (10499/10000*X)⌋₊+1)).filter (fun n=>Real.exp (1001/1000*X) ≤ n)
lemma yF (X:ℝ) (n:ℕ) :
    n ∈ f5 X ↔ Real.exp (1001/1000*X) ≤ n ∧ (n:ℝ) ≤ Real.exp (10499/10000*X):=by
  simp only [f5,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.exp_pos _).le,and_comm]
lemma Ez {X:ℝ} (hX:0 < X) (n:ℕ)
    (hn:n ≠ 0) (hout:n ∉ f5 X) :
    Polynomial.eval (Real.exp (-Real.log n/X)) gN ≤ 0:=by
  have hnp:(0:ℝ) < n:=by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog:0 ≤ Real.log n:=Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  apply lT
  · exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  rw [yF,not_and_or] at hout
  rcases hout with hl | hr
  · right
    have:Real.log n < 1001/1000*X:=(Real.log_lt_iff_lt_exp hnp).mpr (lt_of_not_ge hl)
    apply Ml.le.trans
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hX).mpr
    linarith
  · left
    have:10499/10000*X < Real.log n:=(Real.lt_log_iff_exp_lt hnp).mpr (lt_of_not_ge hr)
    apply le_trans _ Mj.le
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hX).mpr
    linarith
lemma ED {q:ℕ} [NeZero q] (a:ZMod q) {X:ℝ} (hX:0 < X) :
    (∑' n,residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) gN) ≤
      ∑ n ∈ f5 X,residueClass a n / n:=by
  classical
  let f:=fun n:ℕ=>if n ∈ f5 X then residueClass a n / n else 0
  have hf:Summable f:=summable_of_ne_finset_zero (s:=f5 X) (by
    intro n hn
    simp [f,hn])
  have ht:(∑' n,f n) = ∑ n ∈ f5 X,residueClass a n / n:=by
    rw [tsum_eq_sum (s:=f5 X) (by intro n hn; simp [f,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [f,hn]
  rw [← ht]
  apply Summable.tsum_le_tsum _ (vV a gN hX) hf
  intro n
  by_cases hn:n = 0
  · subst n
    simp [f]
  have hlog:0 ≤ Real.log n:=Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hy:Real.exp (-Real.log n/X) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog) hX.le)⟩
  have hw:0 ≤ residueClass a n / n:=div_nonneg (residueClass_nonneg a n) (Nat.cast_nonneg n)
  by_cases hm:n ∈ f5 X
  · simp only [f,dO hm]
    calc
      _ ≤ residueClass a n / n * Real.exp (-Real.log n/X):=by
        exact mul_le_of_le_one_right (mul_nonneg hw hy.1) (BZ hy)
      _ ≤ _:=mul_le_of_le_one_right hw hy.2
  · simp only [f,gR hm]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hw hy.1) (Ez hX n hn hm)
theorem r7 {q:ℕ} [NeZero q] {a:ZMod q} (ha:IsUnit a) :
    ∃ c:ℝ,0 < c ∧ ∀ᶠ X:ℝ in atTop,
      c*X ≤ ∑ n ∈ f5 X,residueClass a n / n:=by
  let c:=(q.totient:ℝ)⁻¹ * (∫ x:ℝ in 0..1,Polynomial.eval x gN)
  have hc:0 < c:=mul_pos (inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero))
    tq
  have hlim:=rG ha gN
  have he:∀ᶠ X:ℝ in atTop,
      c/2 < ∑ j ∈ gN.support,gN.coeff j *
        ((∑' n,residueClass a n / (n:ℝ)^(1+(j+1:ℝ)/X)) / X) :=
    hlim.eventually (eventually_gt_nhds (by dsimp [c]; linarith only [hc]:c/2 < c))
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with X h hX
  have hid:=zj a gN hX
  have h':c/2 < (∑' n,residueClass a n / n * Real.exp (-Real.log n/X) *
      Polynomial.eval (Real.exp (-Real.log n/X)) gN) / X:=by
    rw [← hid,Finset.sum_div]
    simpa only [mul_div_assoc] using h
  exact ((lt_div_iff₀ hX).mp h').le.trans (ED a hX)
theorem u9 {q:ℕ} [NeZero q] {a:ZMod q} (ha:IsUnit a) :
    ∃ c:ℝ,0 < c ∧ ∀ᶠ X:ℝ in atTop,
      c*X ≤ ∑ n ∈ (f5 X).filter Nat.Prime,residueClass a n / n:=by
  classical
  obtain ⟨c,hc,he⟩:=r7 ha
  let f:ℕ → ℝ:=fun n=>(if n.Prime then 0 else residueClass a n) / n
  have hf:Summable f:=summable_residueClass_non_primes_div a
  have hn:∀ n,0 ≤ f n:=by intro n; dsimp [f]; split_ifs <;> positivity [residueClass_nonneg a n]
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [he,eventually_ge_atTop (2*(∑' n,f n)/c)] with X hX hK
  have hb:=hf.sum_le_tsum (f5 X) (fun n _=>hn n)
  have hid:(∑ n ∈ f5 X,residueClass a n/n) =
      (∑ n ∈ (f5 X).filter Nat.Prime,residueClass a n/n) +
      ∑ n ∈ f5 X,f n:=by
    rw [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f]
    split_ifs <;> simp
  rw [hid] at hX
  have Zm:=(div_le_iff₀ hc).mp hK
  nlinarith
end dS
theorem zA {π:GaussianInt} {p:ℕ}
    (hp:p.Prime) (hn:π.norm = (p:ℤ)):Irreducible π:=by
  have hnp:π.norm.natAbs = p:=by rw [hn]; simp
  constructor
  · intro hu
    have h:=Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hnp] at h
    exact hp.ne_one h
  · intro a b hab
    have he:a.norm.natAbs*b.norm.natAbs = p:=by
      rw [← Int.natAbs_mul,← Zsqrtd.norm_mul,← hab,hnp]
    have hi:Irreducible p:=(Nat.irreducible_iff_nat_prime p).mpr hp
    rcases hi.isUnit_or_isUnit he.symm with ha | hb
    · left
      apply Zsqrtd.norm_eq_one_iff.mp
      simpa only [Nat.isUnit_iff] using ha
    · right
      apply Zsqrtd.norm_eq_one_iff.mp
      simpa only [Nat.isUnit_iff] using hb
theorem tQ {p:ℕ} (hp:p.Prime) (hmod:p % 4 = 1) :
    ∃ π:GaussianInt,Irreducible π ∧ π.norm = (p:ℤ):=by
  let:Fact p.Prime:=⟨hp⟩
  have hnp:¬ Irreducible (p:GaussianInt):=by
    intro hi
    have h:=(GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mp hi.prime
    omega
  obtain ⟨a,b,hab⟩:=GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hnp
  have hn:(⟨a,b⟩:GaussianInt).norm = (p:ℤ):=by
    simp only [Zsqrtd.norm]
    norm_num only [Int.reduceNeg,neg_mul,sub_neg_eq_add]
    have h:(a:ℤ)^2+(b:ℤ)^2 = (p:ℤ):=by exact_mod_cast hab
    simpa only [pow_two,one_mul] using h
  exact ⟨⟨a,b⟩,zA hp hn,hn⟩
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD dD g4 c9 oG
namespace GaussianMoat
open Filter Topology Finset
namespace aD
open scoped BigOperators
variable {Ω:Type bU} {α:Type cD} [Fintype Ω] {k:ℕ}
theorem lC {β:Type dD} {γ:Type g4} (p:aD Ω)
    (X:Ω → α) (Y:Ω → β) (C:Ω → γ)
    (h:∀ ω ν,C ω = C ν → (X ω = X ν ↔ Y ω = Y ν)) :
    p.bT X C = p.bT Y C:=by
  unfold bT
  congr 1
  apply p.aZ
  intro ω ν
  simp only [Prod.mk.injEq]
  constructor <;> intro hh
  · exact ⟨(h ω ν hh.2).mp hh.1,hh.2⟩
  · exact ⟨(h ω ν hh.2).mpr hh.1,hh.2⟩
theorem nQ {β:Type dD} {γ:Type g4} (p:aD Ω)
    (X:Ω → α) (Y:Ω → β) (C:Ω → γ)
    (h:∀ ω ν,Y ω = Y ν → C ω = C ν → X ω = X ν) :
    p.bT X C ≤ p.bT Y C:=by
  apply sub_le_sub_right
  apply p.lN
  intro ω ν hh
  rcases Prod.mk.inj hh with ⟨hy,hc⟩
  exact Prod.ext (h ω ν hy hc) hc
theorem K8 {ι:Type c9} {β:Type dD} (p:aD Ω)
    (X:Ω → ι → α) (C:Ω → β) (S:Finset ι) :
    p.bT (fun ω (i:S)=>X ω i) C ≤ ∑ i ∈ S,p.bT (fun ω=>X ω i) C:=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he:p.bT (fun ω (i:(∅:Finset ι))=>X ω i) C = p.bT (fun _=>()) C:=by
      apply p.lC
      intro ω ν _
      simp only [iff_true]
      funext i
      exact False.elim (Finset.notMem_empty i.val i.property)
    have hc:p.bT (fun _=>()) C = 0:=by
      unfold bT
      have hh:=p.aZ (fun ω=>((),C ω)) C (fun _ _=>by simp)
      rw [hh,sub_self]
    simp [he,hc]
  | @insert i S hi ih =>
    have he:p.bT (fun ω (j:(insert i S:Finset ι))=>X ω j) C =
        p.bT (fun ω=>(X ω i,fun j:S=>X ω j)) C:=by
      apply p.lC
      intro ω ν _
      constructor
      · intro h
        apply Prod.ext
        · exact congrFun h ⟨i,Finset.mem_insert_self _ _⟩
        · funext j; exact congrFun h ⟨j,Finset.mem_insert_of_mem j.property⟩
      · intro h
        funext j
        rcases Finset.mem_insert.mp j.property with hj | hj
        · simpa [hj] using congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) ⟨j,hj⟩
    rw [he,Finset.sum_insert hi]
    have hh:=p.C9 (fun ω=>X ω i) (fun ω (j:S)=>X ω j) C
    linarith
theorem l6 {ι:Type c9} {β:Type dD} [Fintype ι] (p:aD Ω)
    (X:Ω → ι → α) (C:Ω → β) :
    p.bT X C ≤ ∑ i,p.bT (fun ω=>X ω i) C:=by
  have h:=p.K8 X C Finset.univ
  have he:p.bT (fun ω (i:(Finset.univ:Finset ι))=>X ω i) C = p.bT X C:=by
    apply p.lC
    intro ω ν _
    exact ⟨fun hh=>funext (fun i=>congrFun hh ⟨i,Finset.mem_univ i⟩),
      fun hh=>funext (fun i=>congrFun hh i)⟩
  rwa [he] at h
omit [Fintype Ω] in
theorem pD (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k)) (s:ℕ)
    (i j:Fin k) (hi:s ≤ i.val) (hj:s ≤ j.val) :
    aF X (π*Equiv.swap i j) s = aF X π s:=by
  classical
  funext ω a
  by_cases ha:a.val<s
  · have hai:a≠i:=by intro he; subst a; omega
    have haj:a≠j:=by intro he; subst a; omega
    simp [aF,ha,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hai haj]
  · simp [aF,ha]
theorem rH {β:Type dD} (p:aD Ω)
    (X:Ω → Fin k → α) (C:Equiv.Perm (Fin k) → Ω → β)
    (i j:Fin k) (hC:∀ π,C (π*Equiv.swap i j) = C π) :
    (𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π i)) (C π)) =
      𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π j)) (C π):=by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  change p.bT (fun ω=>X ω (π i)) (C π) =
    p.bT (fun ω=>X ω ((π*Equiv.swap i j) j)) (C (π*Equiv.swap i j))
  rw [hC]
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]
theorem AG {β:Type dD} (p:aD Ω)
    (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k)) (C:Ω → β)
    {b q:ℕ} (hbq:b ≤ q) (hq:q ≤ k)
    (hC:∀ ω ν,C ω = C ν → aF X π b ω = aF X π b ν) :
    p.bT (aF X π q) C ≤
      ∑ j:Fin (q-b),p.bT (fun ω=>X ω (π ⟨b+j.val,by omega⟩)) C:=by
  let R:=fun ω (j:Fin (q-b))=>X ω (π ⟨b+j.val,by omega⟩)
  apply (p.nQ (aF X π q) R C ?_).trans
    (p.l6 R C)
  intro ω ν hR hcond
  funext i
  by_cases hi:i.val < b
  · have h:=congrFun (hC ω ν hcond) i
    simpa [aF,hi,show i.val<q by omega] using h
  by_cases hiq:i.val < q
  · have h:=congrFun hR ⟨i.val-b,by omega⟩
    have hidx:(⟨b+(i.val-b),by omega⟩:Fin k) = i:=by
      apply Fin.ext
      change b+(i.val-b)=i.val
      omega
    simpa only [R,hidx,aF,hiq,dO] using congrArg some h
  · simp [aF,hiq]
theorem lD {β:Type dD} (p:aD Ω)
    (X:Ω → Fin k → α) (C:Equiv.Perm (Fin k) → Ω → β)
    {b q:ℕ} (hbq:b < q) (hq:q ≤ k)
    (hC:∀ π ω ν,C π ω = C π ν → aF X π b ω = aF X π b ν)
    (hswap:∀ π (j:Fin k),b ≤ j.val →
      C (π*Equiv.swap ⟨b,by omega⟩ j) = C π) :
    (𝔼 π:Equiv.Perm (Fin k),p.bT (aF X π q) (C π)) ≤
      (q-b:ℕ) * (𝔼 π:Equiv.Perm (Fin k),
        p.bT (fun ω=>X ω (π ⟨b,by omega⟩)) (C π)):=by
  have h:=Finset.expect_le_expect (s:=Finset.univ) (fun π _ =>
    p.AG X π (C π) hbq.le hq (hC π))
  rw [Finset.expect_sum_comm] at h
  have he (j:Fin (q-b)) :
      (𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π ⟨b+j.val,by omega⟩)) (C π)) =
      𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π ⟨b,by omega⟩)) (C π):=by
    exact (p.rH X C ⟨b,by omega⟩ ⟨b+j.val,by omega⟩
      (fun π=>hswap π _ (by change b ≤ b+j.val; omega))).symm
  simpa only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
theorem tw {β:Type dD} {γ:Type g4} {δ:Type oG} (p:aD Ω)
    (X Y Z:Ω → Fin k → α) (d:Ω → Fin k → β) (H:Ω → γ) (E:Ω → δ)
    {b q:ℕ} (hb:0 < b) (hbq:b < q) (hq:q ≤ k)
    (hd:∀ i ω ν,X ω i = X ν i → Y ω i = Y ν i → d ω i = d ν i)
    (hY:∀ i ω ν,X ω i = X ν i → d ω i = d ν i → Y ω i = Y ν i)
    (hH:∀ i ω ν,H ω = H ν → d ω i = d ν i)
    (hZ:∀ i ω ν,X ω i = X ν i → E ω = E ν → Z ω i = Z ν i) :
    (b:ℝ) * ((q-b:ℕ) *
      (𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>d ω (π ⟨b,by omega⟩))
        (fun ω=>(aF X π b ω,aF Y π b ω))) +
      p.bF Z q-p.Hf H-p.Hf E) ≤
      (q:ℝ)*(p.bF X b+p.bF Y b):=by
  let C:=fun (π:Equiv.Perm (Fin k)) ω =>
    ((aF X π b ω,aF Y π b ω),H ω)
  let A:=𝔼 π:Equiv.Perm (Fin k),
    p.bT (fun ω=>X ω (π ⟨b,by omega⟩)) (C π)
  let F:=𝔼 π:Equiv.Perm (Fin k),
    p.bT (fun ω=>d ω (π ⟨b,by omega⟩))
      (fun ω=>(aF X π b ω,aF Y π b ω))
  have JX:=p.lD X C hbq hq
    (fun π ω ν hh=>congrArg (fun c=>c.1.1) hh) (by
      intro π j hj
      dsimp [C]
      rw [pD X π b _ j (by exact le_rfl) hj,
        pD Y π b _ j (by exact le_rfl) hj])
  have kT (π:Equiv.Perm (Fin k)) :
      p.Hf (aF Z π q)-p.Hf E-p.Hf (aF X π b)-
        p.Hf (aF Y π b)-p.Hf H ≤ p.bT (aF X π q) (C π):=by
    have hz:p.Hf (aF Z π q) ≤ p.Hf (aF X π q)+p.Hf E:=by
      apply (p.lN (aF Z π q)
        (fun ω=>(aF X π q ω,E ω)) ?_).trans (p.kJ _ _)
      intro ω ν hh
      funext i
      by_cases hi:i.val<q
      · have hx:X ω (π i)=X ν (π i):=by
          simpa [aF,hi] using congrFun (congrArg Prod.fst hh) i
        simpa only [aF,hi,dO] using congrArg some
          (hZ (π i) ω ν hx (congrArg Prod.snd hh))
      · simp [aF,hi]
    have hc:p.Hf (C π) ≤ p.Hf (aF X π b)+p.Hf (aF Y π b)+p.Hf H:=by
      have h1:=p.kJ (fun ω=>(aF X π b ω,aF Y π b ω)) H
      have h2:=p.kJ (aF X π b) (aF Y π b)
      dsimp [C]
      linarith
    have hx:=p.kH (C π) (aF X π q)
    rw [p.kd] at hx
    unfold bT
    linarith
  have hav:=Finset.expect_le_expect (s:=Finset.univ) (fun π _=>kT π)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hal:p.bF Z q-p.Hf E-p.bF X b-
      p.bF Y b-p.Hf H ≤ (q-b:ℕ)*A:=hav.trans JX
  have hchain:=Finset.expect_le_expect (s:=Finset.univ) (fun π _ =>
    p.Mh (fun ω=>X ω (π ⟨b,by omega⟩)) (fun ω=>Y ω (π ⟨b,by omega⟩))
      (aF X π b) (aF Y π b) (fun ω=>d ω (π ⟨b,by omega⟩)) H
      (hd _) (hY _) (hH _))
  simp only [Finset.expect_sub_distrib,Finset.expect_add_distrib] at hchain
  have Yv:F ≤ (p.bF X (b+1)-p.bF X b)+
      (p.bF Y (b+1)-p.bF Y b)-A:=by
    rwa [p.lO X (by omega),p.lO Y (by omega)]
  have hx:=p.nP X hb (by omega)
  have hy:=p.nP Y hb (by omega)
  have haux:A+F ≤ (p.bF X b+p.bF Y b)/b:=by
    rw [add_div]
    linarith
  have hbR:(0:ℝ)<b:=by exact_mod_cast hb
  have YH:(0:ℝ)≤(q-b:ℕ):=by positivity
  have hm:=mul_le_mul_of_nonneg_left haux YH
  have Uv:=mul_le_mul_of_nonneg_left hm hbR.le
  have hn:((q-b:ℕ):ℝ) = q-b:=by rw [Nat.cast_sub hbq.le]
  have hdiv:(b:ℝ)*((q-b:ℕ)*((p.bF X b+p.bF Y b)/b)) =
      (q-b:ℕ)*(p.bF X b+p.bF Y b):=by field_simp
  rw [hdiv] at Uv
  have U7:=mul_le_mul_of_nonneg_left hal hbR.le
  change (b:ℝ)*((q-b:ℕ)*F+p.bF Z q-p.Hf H-p.Hf E) ≤ _
  rw [hn] at Uv U7 ⊢
  nlinarith
end aD
open scoped BigOperators
lemma r8 {ι:Type c9} [Fintype ι] [DecidableEq ι] (f:ι → ℝ) (i j:ι) :
    (𝔼 π:Equiv.Perm ι,f (π i)) = 𝔼 π:Equiv.Perm ι,f (π j):=by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  change f (π i) = f ((π*Equiv.swap i j) j)
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]
theorem DA {ι:Type c9} [Fintype ι] [DecidableEq ι] (f:ι → ℝ)
    (hf:∑ i,f i = 0) {i j:ι} (hij:i ≠ j) :
    (𝔼 π:Equiv.Perm ι,f (π i)*f (π j)) ≤ 0:=by
  classical
  let S:=Finset.univ.erase i
  have hS:S.Nonempty:=⟨j,Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩⟩
  have hex (a:ι) (ha:a ∈ S) :
      (𝔼 π:Equiv.Perm ι,f (π i)*f (π a)) =
        𝔼 π:Equiv.Perm ι,f (π i)*f (π j):=by
    have hai:i ≠ a:=(Finset.mem_erase.mp ha).1.symm
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap a j))
    intro π
    change f (π i)*f (π a) = f ((π*Equiv.swap a j) i)*f ((π*Equiv.swap a j) j)
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hai hij]
  have hsum (π:Equiv.Perm ι):(∑ a ∈ S,f (π a)) = -f (π i):=by
    have h:=Equiv.sum_comp π f
    rw [hf] at h
    have hi:=Finset.sum_erase_add (s:=Finset.univ) (f:=fun a=>f (π a))
      (Finset.mem_univ i)
    dsimp [S]
    linarith
  have hid:(S.card:ℝ)*(𝔼 π:Equiv.Perm ι,f (π i)*f (π j)) =
      -(𝔼 π:Equiv.Perm ι,f (π i)^2):=by
    calc
      _ = ∑ a ∈ S,(𝔼 π:Equiv.Perm ι,f (π i)*f (π a)):=by
        rw [show (∑ a ∈ S,(𝔼 π:Equiv.Perm ι,f (π i)*f (π a))) =
            ∑ _a ∈ S,(𝔼 π:Equiv.Perm ι,f (π i)*f (π j)) from
              Finset.sum_congr rfl (fun a ha=>hex a ha)]
        simp [nsmul_eq_mul]
      _ = 𝔼 π:Equiv.Perm ι,∑ a ∈ S,f (π i)*f (π a) :=
        (Finset.expect_sum_comm _ _ _).symm
      _ = -(𝔼 π:Equiv.Perm ι,f (π i)^2):=by
        simp_rw [← Finset.mul_sum,hsum,mul_neg,← sq]
        rw [Finset.expect_neg_distrib]
  have TA:0 ≤ (𝔼 π:Equiv.Perm ι,f (π i)^2) :=
    Finset.expect_nonneg (fun _ _=>sq_nonneg _)
  have hc:(0:ℝ) < S.card:=by exact_mod_cast hS.card_pos
  nlinarith
theorem zC {ι:Type c9} [Fintype ι] [DecidableEq ι] (f:ι → ℝ)
    (hf:∑ i,f i = 0) (S:Finset ι) {M:ℝ} (hM:∀ i,(f i)^2 ≤ M) :
    (𝔼 π:Equiv.Perm ι,(∑ i ∈ S,f (π i))^2) ≤ S.card*M:=by
  classical
  induction S using Finset.induction_on with
  | empty=>simp
  | @insert i S hi ih =>
    have hsqr (π:Equiv.Perm ι):(∑ j ∈ insert i S,f (π j))^2 =
        (f (π i))^2+(∑ j ∈ S,f (π j))^2+2*(∑ j ∈ S,f (π i)*f (π j)):=by
      rw [Finset.sum_insert hi,← Finset.mul_sum]
      ring
    simp_rw [hsqr,Finset.expect_add_distrib,← Finset.mul_expect,Finset.expect_sum_comm]
    have hb:(𝔼 π:Equiv.Perm ι,f (π i)^2) ≤ M :=
      (Finset.expect_le_expect (s:=Finset.univ) (fun π _=>hM (π i))).trans_eq
        (Fintype.expect_const _)
    have hc:(∑ j ∈ S,(𝔼 π:Equiv.Perm ι,f (π i)*f (π j))) ≤ 0:=by
      apply Finset.sum_nonpos
      intro j hj
      exact DA f hf (fun he=>hi (he.symm ▸ hj))
    rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    nlinarith
theorem Gb {Ω:Type bU} [Fintype Ω] [Nonempty Ω]
    (Z:Ω → ℝ) {a δ V:ℝ} (hδ:0 < δ)
    (hV:(𝔼 ω,(Z ω-a)^2) ≤ V) :
    (𝔼 ω,if Z ω < a-δ then (1:ℝ) else 0) ≤ V/δ^2:=by
  classical
  have he:∀ ω,δ^2*(if Z ω < a-δ then (1:ℝ) else 0) ≤ (Z ω-a)^2:=by
    intro ω
    split_ifs with hh
    · nlinarith
    · simpa using sq_nonneg (Z ω-a)
  have h:=Finset.expect_le_expect (s:=Finset.univ) (fun ω _=>he ω)
  rw [← Finset.mul_expect] at h
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by nlinarith)
theorem zD {ι:Type c9} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f:ι → ℝ) (S:Finset ι) {a M δ:ℝ} (hδ:0 < δ)
    (hf:∀ i,a ≤ f i ∧ f i ≤ a+M) :
    (𝔼 π:Equiv.Perm ι,
      if (∑ i ∈ S,f (π i)) < S.card*(𝔼 i,f i)-δ then (1:ℝ) else 0) ≤
      S.card*M^2/δ^2:=by
  let μ:=𝔼 i,f i
  have hlo:a ≤ μ:=by
    have h:=Finset.expect_le_expect (s:=Finset.univ) (fun i _=>(hf i).1)
    simpa only [Fintype.expect_const] using h
  have hhi:μ ≤ a+M:=by
    have h:=Finset.expect_le_expect (s:=Finset.univ) (fun i _=>(hf i).2)
    simpa only [Fintype.expect_const] using h
  have hsum:∑ i,(f i-μ) = 0:=by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [show (Fintype.card ι:ℝ)*μ = ∑ i,f i from Fintype.card_mul_expect f]
    ring
  have hsq (i:ι):(f i-μ)^2 ≤ M^2:=by
    have h:=hf i
    nlinarith
  have TA:=zC (fun i=>f i-μ) hsum S hsq
  have hid (π:Equiv.Perm ι):(∑ i ∈ S,(f (π i)-μ)) =
      (∑ i ∈ S,f (π i))-S.card*μ:=by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  simp_rw [hid] at TA
  exact Gb _ hδ TA
namespace aD
open scoped BigOperators
variable {Ω:Type bU} {α:Type cD} [Fintype Ω] {k:ℕ}
noncomputable def uniform (Ω:Type bU) [Fintype Ω] [Nonempty Ω]:aD Ω where
  mass:=fun _=>(Fintype.card Ω:ℝ)⁻¹
  nonneg:=fun _=>inv_nonneg.mpr (Nat.cast_nonneg _)
  dN:=by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos:0 < Fintype.card Ω).ne')
@[simp] theorem m4 [Nonempty Ω] (ω:Ω) :
    uniform Ω ω = (Fintype.card Ω:ℝ)⁻¹:=rfl
theorem Gd {β:Type dD} [Nonempty Ω] (X:Ω → β)
    (hX:Function.Injective X):(uniform Ω).Hf X = Real.log (Fintype.card Ω):=by
  classical
  have hN:(Fintype.card Ω:ℝ) ≠ 0:=by exact_mod_cast (Fintype.card_pos:0 < Fintype.card Ω).ne'
  unfold Hf
  simp only [hX.eq_iff,m4,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Real.log_inv]
  rw [← mul_assoc,mul_inv_cancel₀ hN]
  ring
theorem kF {β:Type dD} [Fintype β] (p:aD Ω) (X:Ω → β) :
    p.Hf X ≤ Real.log (Fintype.card β):=by
  rw [p.jW]
  exact (p.map X).lK
theorem vW {β:Type dD} (p:aD Ω) (X:Ω → β)
    (S:Finset β) (hX:∀ ω,X ω ∈ S):p.Hf X ≤ Real.log S.card:=by
  classical
  let Y:=fun ω=>(⟨X ω,hX ω⟩:S)
  have he:p.Hf X = p.Hf Y:=by
    apply p.aZ
    intro ω ν
    exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  rw [he]
  simpa using p.kF Y
theorem U8 {ι:Type c9} {β:Type dD} [Fintype ι] [Fintype β]
    (p:aD ι) (q:ι → aD Ω) (X:Ω → β) :
    (p.mix q).map X = p.mix (fun i=>(q i).map X):=by
  classical
  apply aD.ext; rintro b
  simp only [f7,kV,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp
theorem Xx {ι:Type c9} {β:Type dD} [Fintype ι]
    (p:aD ι) (q:ι → aD Ω) (X:Ω → β) :
    (∑ i,p i*(q i).Hf X) ≤ (p.mix q).Hf X:=by
  classical
  let Y:=fun ω=>(⟨X ω,⟨ω,rfl⟩⟩:Set.range X)
  let:Fintype (Set.range X):=Fintype.ofFinite _
  have he (r:aD Ω):r.Hf X = r.Hf Y:=by
    apply r.aZ
    intro ω ν
    exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  simp_rw [he,jW]
  change (∑ i,p i*((q i).map Y).entropy) ≤ ((p.mix q).map Y).entropy
  rw [U8]
  exact p.Ou _
theorem VY (p:aD Ω) (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k))
    (s:ℕ):p.Hf (aF X π s) ≤ p.Hf X:=by
  exact p.lN _ _ (fun ω ν hh =>
    congrArg (fun y (i:Fin k)=>if i.val < s then some (y (π i)) else none) hh)
theorem La {ι:Type c9} {β:Type dD} [Fintype ι] (p:aD Ω)
    (X:Ω → ι → β):p.Hf X ≤ ∑ i,p.Hf (fun ω=>X ω i):=by
  classical
  have he:p.Hf (fun ω (i:(Finset.univ:Finset ι))=>X ω i) = p.Hf X:=by
    apply p.aZ
    intro ω ν
    constructor
    · intro hh
      funext i
      exact congrFun hh ⟨i,Finset.mem_univ _⟩
    · intro hh
      funext i
      exact congrFun hh i
  simpa only [he] using p.Me X Finset.univ
theorem Mr (p:aD Ω) (X:Ω → Fin k → α)
    (L:Fin k → ℝ) (hL:∀ i,p.Hf (fun ω=>X ω i) ≤ L i)
    (π:Equiv.Perm (Fin k)) {s:ℕ} (hs:s ≤ k) :
    p.Hf (aF X π s) ≤ ∑ j:Fin s,L (π ⟨j.val,by omega⟩):=by
  let Y:=fun ω (j:Fin s)=>X ω (π ⟨j.val,by omega⟩)
  have he:p.Hf (aF X π s) = p.Hf Y:=by
    apply p.aZ
    intro ω ν
    constructor
    · intro hh
      funext j
      have h:=congrFun hh ⟨j.val,by omega⟩
      simpa [aF,j.isLt,Y] using h
    · intro hh
      funext j
      by_cases hj:j.val < s
      · have h:=congrFun hh ⟨j.val,hj⟩
        simpa [aF,hj,Y] using congrArg some h
      · simp [aF,hj]
  rw [he]
  exact (p.La Y).trans (Finset.sum_le_sum (fun j _=>hL _))
theorem zE {β:Type dD} (p:aD Ω)
    (X Y:Ω → Fin k → α) (d:Ω → Fin k → β) {b s:ℕ}
    (hbs:b < s) (hs:s ≤ k)
    (hd:∀ i ω ν,X ω i = X ν i → Y ω i = Y ν i → d ω i = d ν i) :
    p.bF d s-p.bF X b-p.bF Y b ≤
      (s-b:ℕ)*(𝔼 π:Equiv.Perm (Fin k),
        p.bT (fun ω=>d ω (π ⟨b,by omega⟩))
          (fun ω=>(aF X π b ω,aF Y π b ω))):=by
  let C:=fun (π:Equiv.Perm (Fin k)) ω=>(aF X π b ω,aF Y π b ω)
  have hdet:∀ π ω ν,C π ω=C π ν → aF d π b ω=aF d π b ν:=by
    intro π ω ν hh
    funext i
    by_cases hi:i.val < b
    · have hx:=congrFun (congrArg Prod.fst hh) i
      have hy:=congrFun (congrArg Prod.snd hh) i
      simp only [C,aF,hi,dO,Option.some.injEq] at hx hy
      simpa only [aF,hi,dO] using congrArg some (hd (π i) ω ν hx hy)
    · simp [aF,hi]
  have JX:=p.lD d C hbs hs hdet (by
    intro π j hj
    dsimp [C]
    rw [pD X π b _ j (by exact le_rfl) hj,
      pD Y π b _ j (by exact le_rfl) hj])
  have kT (π:Equiv.Perm (Fin k)):p.Hf (aF d π s)-
      p.Hf (aF X π b)-p.Hf (aF Y π b) ≤
        p.bT (aF d π s) (C π):=by
    have h1:=p.kJ (aF X π b) (aF Y π b)
    have h2:=p.kH (C π) (aF d π s)
    rw [p.kd] at h2
    dsimp [C] at *
    unfold bT
    linarith
  have hav:=Finset.expect_le_expect (s:=Finset.univ) (fun π _=>kT π)
  simp only [Finset.expect_sub_distrib] at hav
  exact hav.trans JX
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open Filter Topology Finset
open scoped BigOperators
namespace dS
open Filter Topology Finset
open ArithmeticFunction.vonMangoldt Complex
open scoped BigOperators
def d6 (j:ℕ):Finset ℕ :=
  (Finset.Ico (2^j) (2^(j+1))).filter (fun p=>p.Prime ∧ p % 4 = 1)
lemma iw (j p:ℕ):p ∈ d6 j ↔
    2^j ≤ p ∧ p < 2^(j+1) ∧ p.Prime ∧ p % 4 = 1:=by
  simp only [d6,Finset.mem_filter,Finset.mem_Ico]
  tauto
lemma Nw (p:ℕ) (hp:p.Prime) (hm:p % 4 = 1) :
    p ∈ d6 (Nat.log 2 p):=by
  rw [iw]
  exact ⟨Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by norm_num) p,hp,hm⟩
lemma pN (S:Finset ℕ) {U:ℝ} (hU:0 ≤ U)
    (hp:∀ p ∈ S,p.Prime ∧ (p:ℝ) ≤ U) :
    (∑ p ∈ S,Real.log p) ≤ Real.log 4*U:=by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x hU)
  rw [Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hpS
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.le_floor_iff hU).mpr (hp p hpS).2,(hp p hpS).1⟩
  · intro p hpS _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hpS).2.one_le)
noncomputable def jF (j:ℕ):ℝ :=
  ∑ p ∈ d6 j,Real.log p/p
lemma Tm (j:ℕ):0 ≤ jF j:=by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (iw _ _ |>.mp hp).2.2.1.one_le))
    (Nat.cast_nonneg _)
lemma Pv (j:ℕ):jF j ≤ 2*Real.log 4:=by
  have hT:(0:ℝ) < 2^j:=pow_pos (by norm_num) _
  have hs:jF j ≤ (∑ p ∈ d6 j,Real.log p)/(2^j:ℝ):=by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have h:=(iw j p).mp hp
    apply div_le_div_of_nonneg_left
    · exact Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)
    · exact hT
    · exact_mod_cast h.1
  have ht:=pN (d6 j) (U:=(2:ℝ)^(j+1))
    (by positivity) (by intro p hp; have h:=(iw j p).mp hp
                        exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  apply hs.trans
  apply (div_le_iff₀ hT).mpr
  rw [pow_succ] at ht
  nlinarith
lemma J4 (j:ℕ):jF j ≤
    (d6 j).card * Real.log ((2:ℝ)^(j+1)) / (2:ℝ)^j:=by
  rw [jF]
  have hT:(0:ℝ) < 2^j:=pow_pos (by norm_num) _
  have hp (p:ℕ) (hp:p ∈ d6 j) :
      Real.log p/p ≤ Real.log ((2:ℝ)^(j+1))/(2:ℝ)^j:=by
    have h:=(iw j p).mp hp
    apply le_trans (div_le_div_of_nonneg_left
      (Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)) hT (by exact_mod_cast h.1))
    apply div_le_div_of_nonneg_right _ hT.le
    exact Real.log_le_log (by exact_mod_cast h.2.2.1.pos) (by exact_mod_cast h.2.1.le)
  have hs:=Finset.sum_le_sum (s:=d6 j) hp
  simpa [Finset.sum_const,nsmul_eq_mul,mul_div_assoc] using hs
theorem Ny (J:Finset ℕ) {X c A:ℝ} (hc:0 < c)
    (hA:0 < A) (hcard:(J.card:ℝ) ≤ A*X)
    (Uw:c*X ≤ ∑ j ∈ J,jF j) :
    c*X/(4*Real.log 4) ≤
      ((J.filter (fun j=>c/(2*A) ≤ jF j)).card:ℝ) ∧
    ∀ j ∈ J.filter (fun j=>c/(2*A) ≤ jF j),
      c/(2*A)*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (d6 j).card:=by
  classical
  let G:=J.filter (fun j=>c/(2*A) ≤ jF j)
  have hlog:0 < Real.log (4:ℝ):=Real.log_pos (by norm_num)
  have hδ:0 < c/(2*A):=div_pos hc (by positivity)
  have ht (j:ℕ) (hj:j ∈ J):jF j ≤
      (if j ∈ G then 2*Real.log 4 else 0)+c/(2*A):=by
    by_cases hg:j ∈ G
    · simp only [hg,dO]
      linarith [Pv j]
    · rw [gR hg,zero_add]
      exact (not_le.mp (fun h=>hg (Finset.mem_filter.mpr ⟨hj,h⟩))).le
  have hs:=Finset.sum_le_sum (s:=J) ht
  have he:(∑ j ∈ J,if j ∈ G then 2*Real.log 4 else 0) = G.card*(2*Real.log 4):=by
    rw [← Finset.sum_filter]
    have hG:J.filter (fun j=>j ∈ G) = G:=by
      ext j
      simp only [G,Finset.mem_filter]
      tauto
    rw [hG]
    simp [nsmul_eq_mul]
  rw [Finset.sum_add_distrib,he,Finset.sum_const,nsmul_eq_mul] at hs
  have jd:(J.card:ℝ)*(c/(2*A)) ≤ c*X/2:=by
    have h:=mul_le_mul_of_nonneg_right hcard hδ.le
    have he:A*X*(c/(2*A))=c*X/2:=by field_simp
    rwa [he] at h
  refine ⟨(div_le_iff₀ (by positivity)).mpr (by dsimp [G] at hs; nlinarith),?_⟩
  intro j hj
  have hg:=(Finset.mem_filter.mp hj).2
  have h:=J4 j
  have hT:(0:ℝ) < 2^j:=pow_pos (by norm_num) _
  have hL:0 < Real.log ((2:ℝ)^(j+1)):=Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  apply (div_le_iff₀ hL).mpr
  have h':=(le_div_iff₀ hT).mp (hg.trans h)
  exact h'
noncomputable def vH (X:ℝ):Finset ℕ :=
  (f5 X).filter (fun p=>p.Prime ∧ p % 4 = 1)
noncomputable def k3 (X:ℝ):Finset ℕ :=
  (vH X).image (Nat.log 2)
lemma J6 (p:ℕ) (hp:p.Prime) :
    residueClass (1:ZMod 4) p = if p % 4 = 1 then Real.log p else 0:=by
  have he:(p:ZMod 4) = 1 ↔ p % 4 = 1:=by
    rw [show (1:ZMod 4) = (1:ℕ) from rfl,ZMod.natCast_eq_natCast_iff]
    rfl
  simp only [residueClass,Set.indicator_apply,Set.mem_ofPred_eq,he,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
lemma Ja (X:ℝ) :
    (∑ p ∈ (f5 X).filter Nat.Prime,residueClass (1:ZMod 4) p/p) ≤
      ∑ j ∈ k3 X,jF j:=by
  classical
  have hres:(∑ p ∈ (f5 X).filter Nat.Prime,residueClass (1:ZMod 4) p/p) =
      ∑ p ∈ vH X,Real.log p/p:=by
    rw [vH,Finset.sum_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp:p.Prime
    · rw [dO hp,J6 p hp]
      by_cases hm:p % 4=1 <;> simp [hp,hm]
    · simp [hp]
  rw [hres,← Finset.sum_fiberwise_of_maps_to
    (s:=vH X) (t:=k3 X) (g:=Nat.log 2)
    (fun p hp=>Finset.mem_image.mpr ⟨p,hp,rfl⟩)]
  apply Finset.sum_le_sum
  intro j _
  dsimp [jF]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hj⟩
    obtain ⟨_,hpp,hpm⟩:=Finset.mem_filter.mp hp
    rw [← hj]
    exact Nw p hpp hpm
  · intro p hp _
    have hpp:=((iw j p).mp hp).2.2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg p)
lemma AH {X:ℝ} (hX:1000 ≤ X) {j:ℕ} (hj:j ∈ k3 X) :
    X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X:=by
  obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hj
  obtain ⟨hpW,hpP,YI⟩:=Finset.mem_filter.mp hp
  have hw:=(yF X p).mp hpW
  have hp0:(0:ℝ) < p:=by exact_mod_cast hpP.pos
  have hlb:=(Real.le_log_iff_exp_le hp0).mpr hw.1
  have hub:=(Real.log_le_iff_le_exp hp0).mpr hw.2
  have RP:=(iw _ _).mp (Nw p hpP YI)
  have kT:=Real.log_le_log (pow_pos (by norm_num:(0:ℝ)<2) (Nat.log 2 p))
    (by exact_mod_cast RP.1:(2:ℝ)^Nat.log 2 p ≤ p)
  have Gh:=Real.log_lt_log hp0
    (by exact_mod_cast RP.2.1:(p:ℝ) < (2:ℝ)^(Nat.log 2 p+1))
  rw [Real.log_pow] at kT Gh
  simp only [Nat.cast_add,Nat.cast_one] at Gh
  constructor
  · nlinarith [Real.log_two_lt_d9]
  · nlinarith
lemma Nz {X:ℝ} (hX:1000 ≤ X):(k3 X).card ≤ 3*X:=by
  classical
  have hX0:0 ≤ X:=by linarith
  have hs:k3 X ⊆ Finset.range (⌊2*X⌋₊+1):=by
    intro j hj
    have h:=(AH hX hj).2
    have hlog:=Real.log_two_gt_d9
    have hj0:(0:ℝ)≤j:=Nat.cast_nonneg _
    have YJ:(j:ℝ)≤2*X:=by nlinarith
    rw [Finset.mem_range,Nat.lt_succ_iff,Nat.le_floor_iff (by positivity:(0:ℝ)≤2*X)]
    exact YJ
  have hc:(k3 X).card ≤ ⌊2*X⌋₊+1 :=
    (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hcR:((k3 X).card:ℝ) ≤ ⌊2*X⌋₊+1:=by exact_mod_cast hc
  have hf:=Nat.floor_le (show (0:ℝ)≤2*X by positivity)
  nlinarith
theorem nF:∃ c δ:ℝ,0 < c ∧ 0 < δ ∧
    ∀ᶠ X:ℝ in atTop,∃ J:Finset ℕ,
      c*X ≤ J.card ∧
      ∀ j ∈ J,X ≤ j*Real.log 2 ∧ j*Real.log 2 ≤ 21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (d6 j).card:=by
  obtain ⟨c,hc,he⟩:=u9 (show IsUnit (1:ZMod 4) from isUnit_one)
  refine ⟨c/(4*Real.log 4),c/6,div_pos hc (by positivity),div_pos hc (by norm_num),?_⟩
  filter_upwards [he,eventually_ge_atTop (1000:ℝ)] with X Uw hX
  let J:=(k3 X).filter (fun j=>c/6 ≤ jF j)
  have hh:=Ny (k3 X) hc (by norm_num:(0:ℝ)<3)
    (Nz hX) (Uw.trans (Ja X))
  refine ⟨J,?_,?_⟩
  · simpa only [show (2:ℝ)*3=6 by norm_num,div_mul_eq_mul_div] using hh.1
  · intro j hj
    have hb:=AH hX (Finset.mem_filter.mp hj).1
    have hd:=hh.2 j (by simpa only [show (2:ℝ)*3=6 by norm_num] using hj)
    exact ⟨hb.1,hb.2,by simpa only [show (2:ℝ)*3=6 by norm_num] using hd⟩
end dS
end GaussianMoat
end OAI
end
section
namespace OAI
universe qC dD c9 bU YM cD
namespace GaussianMoat
open scoped BigOperators Classical
theorem NA {κ:Type qC} {β:Type dD} [Fintype κ] [Fintype β] [Nonempty β]
    (s:Finset κ) (F:(s → β) → ℝ) :
    (𝔼 σ:κ → β,F (fun p=>σ p)) = 𝔼 τ:s → β,F τ:=by
  classical
  let e:=Equiv.piEquivPiSubtypeProd (fun x=>x ∈ s) (fun _=>β)
  calc
    _ = 𝔼 pair:(s → β) × ({x:κ // x ∉ s} → β),F pair.1:=by
      exact Fintype.expect_equiv e _ _ (fun _=>rfl)
    _ = _:=by
      rw [← Finset.univ_product_univ,Finset.expect_product]
      simp only [Fintype.expect_const]
theorem AO {ι:Type c9} {κ:Type qC} {β:Type dD} [Fintype ι] [Fintype κ]
    [Fintype β] [Nonempty β] (e:ι → κ) (he:Function.Injective e)
    (F:(ι → β) → ℝ) :
    (𝔼 σ:κ → β,F (σ ∘ e)) = 𝔼 τ:ι → β,F τ:=by
  classical
  let s:=Finset.univ.image e
  let ee:ι ≃ s:=Equiv.ofBijective (fun i=>⟨e i,Finset.mem_image.mpr
    ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨fun i j h=>he (congrArg Subtype.val h),by
      rintro ⟨y,hy⟩
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hy
      exact ⟨i,Subtype.ext hi⟩⟩
  calc
    _ = 𝔼 τ:s → β,F (fun i=>τ (ee i)):=NA s _
    _ = _:=by
      exact Fintype.expect_equiv (Equiv.arrowCongr ee.symm (Equiv.refl β)) _ _ (fun _=>rfl)
lemma wW {ι:Type c9} [Fintype ι] (S:Set (ι → Bool)) :
    (gY ι).real S = 𝔼 σ:ι → Bool,if σ ∈ S then (1:ℝ) else 0:=by
  rw [rV]
  simp [Finset.expect,NNRat.smul_def,div_eq_inv_mul]
lemma B8 {ι:Type c9} {κ:Type qC} [Fintype ι] [Fintype κ]
    (e:ι → κ) (he:Function.Injective e) (S:Set (ι → Bool)) :
    (𝔼 σ:κ → Bool,if σ ∘ e ∈ S then (1:ℝ) else 0) =
      (gY ι).real S:=by
  exact (AO e he (fun τ=>if τ ∈ S then (1:ℝ) else 0)).trans
    (wW S).symm
lemma vX {Ω:Type bU} {Ξ:Type YM} {α:Type cD} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ] (X:Ξ → Ω → α) (bad:Ξ → Prop)
    (hg:∀ σ,¬bad σ → Function.Injective (X σ)) :
    (1-(𝔼 σ,if bad σ then (1:ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      𝔼 σ,(aD.uniform Ω).Hf (X σ):=by
  have hp (σ:Ξ):(1-(if bad σ then (1:ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      (aD.uniform Ω).Hf (X σ):=by
    by_cases hb:bad σ
    · simpa [hb] using (aD.uniform Ω).JQ (X σ)
    · simp only [hb,ite_false,sub_zero,one_mul]
      rw [aD.Gd _ (hg σ hb)]
  have h:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _=>hp σ)
  simpa only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] using h
abbrev aE.restrict (s:aE) (Q:Finset ℕ) (hQ:Q ⊆ s.primes):aE where
  primes:=Q
  factor:=s.factor
  iF:=fun p hp=>s.iF p (hQ hp)
  Fy:=fun p hp=>s.Fy p (hQ hp)
  jA:=fun p hp=>s.jA p (hQ hp)
  jc:=fun p hp=>s.jc p (hQ hp)
noncomputable def aE.enumeration (s:aE):Fin s.primes.card ≃ s.primes :=
  s.primes.equivFin.symm
noncomputable def kW (k r:ℕ):Finset (Fin k) :=
  Finset.univ.filter (fun i=>i.val < r)
lemma yI {k r:ℕ} (i:Fin k):i ∈ kW k r ↔ i.val < r:=by
  simp [kW]
lemma vY {k r:ℕ} (hr:r ≤ k):(kW k r).card = r:=by
  have he:kW k r = (Finset.univ:Finset (Fin r)).image
      (fun i=>(⟨i.val,by omega⟩:Fin k)):=by
    ext i
    simp only [yI,Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun hi=>⟨⟨i.val,hi⟩,rfl⟩,fun ⟨j,hj⟩=>by cases hj; exact j.isLt⟩
  have hinj:Function.Injective (fun i:Fin r=>(⟨i.val,by omega⟩:Fin k)) :=
    fun i j h=>Fin.ext (congrArg (fun j:Fin k=>j.val) h)
  rw [he,Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin r
noncomputable def aE.oK (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ):Finset ℕ :=
  (kW s.primes.card r).image (fun i=>(s.enumeration (π i)).val)
lemma aE.qQ (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ):s.oK π r ⊆ s.primes:=by
  intro p hp
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
  exact (s.enumeration (π i)).property
lemma aE.OC (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) {r:ℕ} (hr:r ≤ s.primes.card) :
    (s.oK π r).card = r:=by
  have hinj:Function.Injective (fun i=>(s.enumeration (π i)).val) :=
    Subtype.val_injective.comp (s.enumeration.injective.comp π.injective)
  rw [aE.oK,Finset.card_image_of_injective _ hinj]
  exact vY hr
noncomputable abbrev aE.j5 (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ):aE :=
  s.restrict (s.oK π r) (s.qQ π r)
noncomputable def aE.bC (s:aE)
    (σ:Fin s.primes.card → Bool) (z:GaussianInt) (i:Fin s.primes.card):ℕ :=
  aR (dG (s.factor (s.enumeration i)) (σ i)) z
noncomputable def aE.k7 (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ) (p:(s.oK π r)):Fin s.primes.card :=
  s.enumeration.symm ⟨p.val,s.qQ π r p.property⟩
lemma aE.EH (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ):Function.Injective (s.k7 π r):=by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun y:s.primes=>(y:ℕ)) (s.enumeration.symm.injective hpq)
lemma aE.wX (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ)
    (σ:Fin s.primes.card → Bool) (Δ:Finset GaussianInt) (Q:Set GaussianInt)
    (hΔ:∀ x ∈ Δ,∀ y ∈ Δ,x-y ∈ Q)
    (hb:¬(s.j5 π r).kG Q (σ ∘ s.k7 π r)) :
    Function.Injective (fun x:Δ=>aD.aF (fun x:Δ=>s.bC σ x) π r x):=by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  apply hb
  refine ⟨x-y,hΔ x x.property y y.property,sub_ne_zero.mpr hne,?_⟩
  apply (s.j5 π r).z6 _ (fun _ h=>h)
  intro p hp
  obtain ⟨i,hi,hp'⟩:=Finset.mem_image.mp hp
  have hres:=congrFun hxy i
  have hiv:=(yI i).mp hi
  simp only [aD.aF,hiv,dO,Option.some.injEq] at hres
  have hidx:s.k7 π r ⟨p,hp⟩ = π i:=by
    apply s.enumeration.injective
    apply Subtype.ext
    simpa only [aE.k7,Equiv.apply_symm_apply] using hp'.symm
  rw [aE.Nl _ _ p hp]
  change dG (s.factor p) (σ (s.k7 π r ⟨p,hp⟩)) ∣ _
  rw [hidx]
  simpa only [aE.bC,hp'] using
      (k9 _ _ _).mp hres
theorem aE.AS (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) {r:ℕ} (hr:r ≤ s.primes.card)
    (Δ:Finset GaussianInt) (wY:Δ.Nonempty)
    {T R W d:ℝ} {e:ℂ} (he:‖e‖=1) (hT:5 ≤ T)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hW:1 ≤ W) (q8:W ≤ R) (hd:0 < d) (hd1:d < 1/4)
    (Qc:R*W ≤ ((s.j5 π r).period:ℝ)^(1-d))
    (cQ:1000 ≤ d^3*r)
    (hΔ:∀ x ∈ Δ,∀ y ∈ Δ,x-y ∈ gC e R W) :
    let:=wY.to_subtype
    (1-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      𝔼 σ:Fin s.primes.card → Bool,
        (aD.uniform Δ).Hf (aD.aF (fun x:Δ=>s.bC σ x) π r):=by
  let:=wY.to_subtype
  let t:=s.j5 π r
  let Q:=gC e R W
  have hc:t.primes.card=r:=s.OC π hr
  have ND:(𝔼 σ:Fin s.primes.card → Bool,
      if t.kG Q (σ ∘ s.k7 π r) then (1:ℝ) else 0) ≤
      Real.exp (-(d^3*r/5120)):=by
    calc
      _ = (gY t.primes).real {τ | t.kG Q τ}:=by
        convert B8 (s.k7 π r) (s.EH π r)
          {τ | t.kG Q τ} using 1
        congr 1
        ext σ; simp
      _ ≤ _:=by
        have ht:=t.LX he hT (fun p hp=>hpT p (s.qQ π r hp))
          hW q8 hd hd1 Qc (by rwa [hc])
        simpa only [hc] using ht
  have hg:=vX
    (fun σ=>aD.aF (fun x:Δ=>s.bC σ x) π r)
    (fun σ=>t.kG Q (σ ∘ s.k7 π r))
    (fun σ hb=>s.wX π r σ Δ Q hΔ hb)
  simp only [Fintype.card_coe] at hg
  have hl:0 ≤ Real.log (Δ.card:ℝ):=Real.log_nonneg (by exact_mod_cast wY.card_pos)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left ND 1) hl).trans hg
noncomputable def aE.aP (s:aE):ℝ :=
  𝔼 i:Fin s.primes.card,Real.log (s.enumeration i:ℕ)
lemma aE.Lb (s:aE)
    (π:Equiv.Perm (Fin s.primes.card)) (r:ℕ) :
    Real.log ((s.j5 π r).period:ℝ) =
      ∑ i ∈ kW s.primes.card r,Real.log (s.enumeration (π i):ℕ):=by
  rw [aE.F3]
  rw [Finset.sum_coe_sort (s.j5 π r).primes (fun p:ℕ=>Real.log (p:ℝ))]
  change (∑ p ∈ s.oK π r,Real.log (p:ℝ)) = _
  unfold aE.oK
  exact Finset.sum_image (Subtype.val_injective.comp
    (s.enumeration.injective.comp π.injective)).injOn
lemma aE.Jb (s:aE) (hk:0 < s.primes.card)
    {r:ℕ} (hr:r ≤ s.primes.card) {T δ:ℝ} (hT:0 < T) (hδ:0 < δ)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T) :
    (𝔼 π:Equiv.Perm (Fin s.primes.card),
      if Real.log ((s.j5 π r).period:ℝ) < r*s.aP-δ then (1:ℝ) else 0) ≤
      r*(Real.log 2)^2/δ^2:=by
  let:Nonempty (Fin s.primes.card):=⟨⟨0,hk⟩⟩
  have hb (i:Fin s.primes.card):Real.log T ≤ Real.log (s.enumeration i:ℕ) ∧
      Real.log (s.enumeration i:ℕ) ≤ Real.log T+Real.log 2:=by
    have hh:=hpT (s.enumeration i) (s.enumeration i).property
    constructor
    · exact Real.log_le_log hT hh.1
    · have h:=Real.log_le_log (hT.trans_le hh.1) hh.2
      rwa [Real.log_mul (by norm_num:(2:ℝ)≠0) hT.ne',add_comm] at h
  have h:=zD (fun i=>Real.log (s.enumeration i:ℕ))
    (kW s.primes.card r) hδ hb
  convert h using 1 <;>
    simp only [vY hr,aE.aP,← s.Lb]
  congr 1
theorem aE.EI (s:aE)
    {r:ℕ} (hr:r ≤ s.primes.card) (Δ:Finset GaussianInt) (wY:Δ.Nonempty)
    {T R W d δ:ℝ} {e:ℂ} (he:‖e‖=1) (hT:5 ≤ T)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hW:1 ≤ W) (q8:W ≤ R) (hd:0 < d) (hd1:d < 1/4)
    (hδ:0 < δ) (jI:Real.log (R*W) ≤ (1-d)*(r*s.aP-δ))
    (cQ:1000 ≤ d^3*r)
    (hΔ:∀ x ∈ Δ,∀ y ∈ Δ,x-y ∈ gC e R W) :
    let:=wY.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      (aD.uniform Δ).gP (fun σ x=>s.bC σ x) r:=by
  let:=wY.to_subtype
  have hk:0 < s.primes.card:=by
    by_contra hn
    have hz:r=0:=by omega
    simp only [hz,Nat.cast_zero,mul_zero] at cQ
    norm_num at cQ
  have Uk:0 < R*W:=mul_pos (by linarith) (by linarith)
  have hlog:0 ≤ Real.log (Δ.card:ℝ):=Real.log_nonneg (by exact_mod_cast wY.card_pos)
  let ε:=Real.exp (-(d^3*r/5120))
  let bad (π:Equiv.Perm (Fin s.primes.card)) :=
    Real.log ((s.j5 π r).period:ℝ) < r*s.aP-δ
  have hp (π:Equiv.Perm (Fin s.primes.card)) :
      (1-(if bad π then (1:ℝ) else 0)-ε)*Real.log Δ.card ≤
      𝔼 σ:Fin s.primes.card → Bool,
        (aD.uniform Δ).Hf (aD.aF (fun x:Δ=>s.bC σ x) π r):=by
    by_cases hb:bad π
    · have hn:0 ≤ (𝔼 σ:Fin s.primes.card → Bool,
          (aD.uniform Δ).Hf (aD.aF (fun x:Δ=>s.bC σ x) π r)) :=
        Finset.expect_nonneg (fun _ _=>(aD.uniform Δ).JQ _)
      simp only [hb,dO,sub_self,zero_sub]
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hlog).trans hn
    · simp only [hb,ite_false,sub_zero]
      apply s.AS π hr Δ wY he hT hpT hW q8 hd hd1 ?_ cQ hΔ
      have hP:0 < ((s.j5 π r).period:ℝ):=by
        exact_mod_cast (s.j5 π r).period_pos
      apply (Real.log_le_log_iff Uk (Real.rpow_pos_of_pos hP _)).mp
      rw [Real.log_rpow hP]
      exact jI.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hb) (by linarith))
  have hav:=Finset.expect_le_expect (s:=Finset.univ) (fun π _=>hp π)
  simp only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hb:=s.Jb hk hr (by linarith:(0:ℝ)<T) hδ hpT
  have kT:=mul_le_mul_of_nonneg_right (sub_le_sub_right (sub_le_sub_left hb 1) ε) hlog
  apply kT.trans
  convert hav using 1
  unfold aD.gP aD.bF
  exact Finset.expect_comm _ _ _
lemma aE.AY {Ω:Type bU} [Fintype Ω]
    (s:aE) (P:aD Ω) (Z:Ω → GaussianInt)
    (σ:Fin s.primes.card → Bool) (i:Fin s.primes.card) :
    P.Hf (fun ω=>s.bC σ (Z ω) i) ≤ Real.log (s.enumeration i:ℕ):=by
  let π:=dG (s.factor (s.enumeration i)) (σ i)
  have hπ:π ≠ 0:=(oD
    (s.jA _ (s.enumeration i).property) _).ne_zero
  obtain ⟨hfin,hcard⟩:=Dz hπ
  have h:=P.vW (fun ω=>aR π (Z ω)) hfin.toFinset
    (fun ω=>hfin.mem_toFinset.mpr ⟨Z ω,rfl⟩)
  rw [← Set.ncard_eq_toFinset_card (Set.range (aR π)) hfin,hcard] at h
  have hn:π.norm.natAbs=(s.enumeration i:ℕ):=by
    dsimp [π]
    rw [iW,s.jc _ (s.enumeration i).property,Int.natAbs_natCast]
  rw [hn] at h
  exact h
lemma aE.oq {Ω:Type bU} [Fintype Ω]
    (s:aE) (P:aD Ω) (Z:Ω → GaussianInt)
    (σ:Fin s.primes.card → Bool) {b:ℕ} (hb:b ≤ s.primes.card)
    {U:ℝ} (hU:∀ p ∈ s.primes,Real.log (p:ℝ) ≤ U) :
    P.bF (fun ω=>s.bC σ (Z ω)) b ≤ b*U:=by
  have h (π:Equiv.Perm (Fin s.primes.card)):=P.Mr
    (fun ω=>s.bC σ (Z ω)) (fun _=>U)
    (fun i=>(s.AY P Z σ i).trans
      (hU _ (s.enumeration i).property)) π hb
  have hh:=Finset.expect_le_expect (s:=Finset.univ) (fun π _=>h π)
  simpa only [aD.bF,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Fintype.expect_const] using hh
theorem aE.Gk (s:aE)
    {b r:ℕ} (hbr:b < r) (hr:r ≤ s.primes.card)
    (Δ:Finset GaussianInt) (wY:Δ.Nonempty)
    (X Y:Δ → GaussianInt) (hXY:∀ ω,X ω-Y ω=ω)
    {T R W d δ:ℝ} {e:ℂ} (he:‖e‖=1) (hT:5 ≤ T)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hW:1 ≤ W) (q8:W ≤ R) (hd:0 < d) (hd1:d < 1/4)
    (hδ:0 < δ) (jI:Real.log (R*W) ≤ (1-d)*(r*s.aP-δ))
    (cQ:1000 ≤ d^3*r)
    (hΔ:∀ x ∈ Δ,∀ y ∈ Δ,x-y ∈ gC e R W) :
    let:=wY.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card-
        2*b*Real.log (2*T) ≤
      (r-b:ℕ)*(𝔼 σ:Fin s.primes.card → Bool,
        𝔼 π:Equiv.Perm (Fin s.primes.card),
          (aD.uniform Δ).bT (fun ω=>s.bC σ ω (π ⟨b,by omega⟩))
            (fun ω=>(aD.aF (fun x=>s.bC σ (X x)) π b ω,
              aD.aF (fun x=>s.bC σ (Y x)) π b ω))):=by
  let:=wY.to_subtype
  let P:=aD.uniform Δ
  have hU (p:ℕ) (hp:p ∈ s.primes):Real.log (p:ℝ) ≤ Real.log (2*T) :=
    Real.log_le_log (by have:=(hpT p hp).1; linarith) (hpT p hp).2
  have hp (σ:Fin s.primes.card → Bool):=P.zE
    (fun ω=>s.bC σ (X ω)) (fun ω=>s.bC σ (Y ω))
    (fun ω=>s.bC σ ω) hbr hr (by
      intro i ω ν hx hy
      change aR _ (ω:GaussianInt) = aR _ (ν:GaussianInt)
      rw [← hXY ω,← hXY ν]
      exact kR hx hy)
  have hX σ:=s.oq P X σ (by omega:b ≤ s.primes.card) hU
  have hY σ:=s.oq P Y σ (by omega:b ≤ s.primes.card) hU
  have hl (σ:Fin s.primes.card → Bool) :
      P.bF (fun ω=>s.bC σ ω) r-2*b*Real.log (2*T) ≤
      (r-b:ℕ)*(𝔼 π:Equiv.Perm (Fin s.primes.card),
        P.bT (fun ω=>s.bC σ ω (π ⟨b,by omega⟩))
          (fun ω=>(aD.aF (fun x=>s.bC σ (X x)) π b ω,
            aD.aF (fun x=>s.bC σ (Y x)) π b ω))):=by
    linarith [hp σ,hX σ,hY σ]
  have hh:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _=>hl σ)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const,← Finset.mul_expect] at hh
  have hg:=s.EI hr Δ wY he hT hpT hW q8 hd hd1 hδ jI cQ hΔ
  exact (sub_le_sub_right hg _).trans hh
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU c9 qC cD dD nW
namespace GaussianMoat
section
open scoped BigOperators Classical
theorem tW {R:ℝ} (hR:1 ≤ R) :
    ((bY R).card:ℝ) ≤ 36*R^2:=by
  have h:=qB (bY R) (e:=1) (c:=(-R:ℝ))
    (by simp) (R:=2*R) (by linarith) hR (by
      intro z hz
      have hn:=(lZ R z).mp hz
      have hr:=abs_le.mp ((Complex.abs_re_le_norm (z:ℂ)).trans hn)
      have hi:=(Complex.abs_im_le_norm (z:ℂ)).trans hn
      simp only [one_mul,Complex.sub_re,Complex.ofReal_re,sub_neg_eq_add,
        Complex.sub_im,Complex.ofReal_im,sub_zero]
      exact ⟨by linarith,by linarith,hi⟩)
  nlinarith
theorem je {Ω:Type bU} [Fintype Ω] (P:aD Ω)
    (Z:Ω → GaussianInt) {R:ℝ} (hR:1 ≤ R) (hZ:∀ ω,‖(Z ω:ℂ)‖ ≤ R) :
    P.Hf Z ≤ Real.log 36+2*Real.log R:=by
  have h:=P.vW Z (bY R) (fun ω=>(lZ R _).mpr (hZ ω))
  have hc:0 < ((bY R).card:ℝ):=by
    exact_mod_cast Finset.card_pos.mpr ⟨0,by simpa using (show 0 ≤ R by linarith)⟩
  have hl:=Real.log_le_log hc (tW hR)
  rw [Real.log_mul (by norm_num:(36:ℝ)≠0) (pow_ne_zero _ (by linarith:R≠0)),
    Real.log_pow] at hl
  exact h.trans hl
theorem EK (E:Finset GaussianInt) {e c:ℂ} {R W:ℝ}
    (hE:∀ p ∈ E,0 ≤ (e*((p:ℂ)-c)).re ∧
      (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W) :
    ∀ x ∈ differences E,∀ y ∈ differences E,
      x-y ∈ gC (star e) (4*R) (4*W):=by
  intro x hx y hy
  obtain ⟨a,ha,b,hb,rfl⟩:=(kQ E x).mp hx
  obtain ⟨a',ha',b',hb',rfl⟩:=(kQ E y).mp hy
  have h1:=hE a ha
  have h2:=hE b hb
  have h3:=hE a' ha'
  have h4:=hE b' hb'
  have heq:e*((a:ℂ)-(b:ℂ)-((a':ℂ)-(b':ℂ))) =
      e*((a:ℂ)-c)-e*((b:ℂ)-c)-(e*((a':ℂ)-c)-e*((b':ℂ)-c)):=by ring
  rw [gC]
  simp only [Set.mem_ofPred_eq,star_star,map_sub,heq,Complex.sub_re,Complex.sub_im]
  obtain ⟨Zq,Zn⟩:=abs_le.mp h1.2.2
  obtain ⟨h2i,h2i'⟩:=abs_le.mp h2.2.2
  obtain ⟨Zr,h3i'⟩:=abs_le.mp h3.2.2
  obtain ⟨Zt,Zo⟩:=abs_le.mp h4.2.2
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith
lemma qE (z:ℕ → GaussianInt) (n:ℕ)
    (d:differences (dK z n)) :
    ∃ ij:Fin (n+1) × Fin (n+1),z ij.1.val-z ij.2.val=d:=by
  obtain ⟨a,ha,b,hb,hab⟩:=(kQ _ _).mp d.property
  obtain ⟨i,hi,rfl⟩:=(j9 _ _ _).mp ha
  obtain ⟨j,hj,rfl⟩:=(j9 _ _ _).mp hb
  exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hab⟩
noncomputable def iz (z:ℕ → GaussianInt) (n:ℕ)
    (d:differences (dK z n)):Fin (n+1) × Fin (n+1) :=
  (qE z n d).choose
lemma kB (z:ℕ → GaussianInt) (n:ℕ)
    (d:differences (dK z n)) :
    z (iz z n d).1.val-z (iz z n d).2.val=d :=
  (qE z n d).choose_spec
lemma Lc (z:ℕ → GaussianInt) (n:ℕ) :
    Function.Injective (iz z n):=by
  intro d d' hh
  apply Subtype.ext
  rw [← kB z n d,← kB z n d',hh]
lemma jU (z:ℕ → GaussianInt) (n:ℕ) :
    (differences (dK z n)).Nonempty:=by
  refine ⟨0,(kQ _ _).mpr ⟨z 0,?_,z 0,?_,sub_self _⟩⟩ <;>
    exact (j9 _ _ _).mpr ⟨0,by omega,rfl⟩
end
namespace aD
open scoped BigOperators Classical
variable {ι:Type c9} {Ω:Type bU} {κ:Type qC} {α:Type cD} {β:Type dD} [Fintype ι] [Fintype Ω] [Fintype κ]
noncomputable def joint (p:aD ι) (q:ι → aD Ω):aD (ι × Ω) where
  mass:=fun v=>p v.1*q v.1 v.2
  nonneg:=fun v=>mul_nonneg (p.nonneg _) ((q _).nonneg _)
  dN:=by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,aD.dN,mul_one]
@[simp] theorem jv (p:aD ι) (q:ι → aD Ω) (i:ι) (ω:Ω) :
    p.joint q (i,ω) = p i*q i ω:=rfl
@[simp] theorem qM (p:aD ι) (q:ι → aD Ω) :
    (p.joint q).map Prod.fst = p:=by
  apply aD.ext; rintro i
  simp only [f7,Fintype.sum_prod_type,jv]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,← Finset.mul_sum,
    dN,mul_one]
@[simp] theorem qN (p:aD ι) (q:ι → aD Ω) :
    (p.joint q).map Prod.snd = p.mix q:=by
  apply aD.ext; rintro ω
  simp [f7,Fintype.sum_prod_type,jv,kV]
@[simp] theorem A8 (p:aD ι) (q:ι → aD Ω) (f:Ω → κ) :
    (p.joint q).map (fun v=>(v.1,f v.2)) = p.joint (fun i=>(q i).map f):=by
  apply aD.ext; rintro ⟨i,x⟩
  simp only [f7,Fintype.sum_prod_type,jv,Prod.mk.injEq,ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp
theorem wZ (p:aD ι) (q:ι → aD Ω) :
    (p.joint q).entropy = p.entropy+∑ i,p i*(q i).entropy:=by
  simp only [entropy,eo,Fintype.sum_prod_type,jv,Real.negMulLog_mul,
    Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,aD.dN,one_mul]
theorem NG (p:aD Ω) (f:Ω → κ) (X:κ → α) :
    (p.map f).Hf X = p.Hf (X ∘ f):=by
  rw [u6,H,map_comp]
  rw [← H,← jW]
  apply p.aZ
  intro ω ν
  exact gO X (f ω) (f ν)
theorem vh (p:aD Ω) (f:Ω → κ) (X:κ → α) (Y:κ → β) :
    (p.map f).bT X Y = p.bT (X ∘ f) (Y ∘ f):=by
  simp only [bT,NG,Function.comp_def]
theorem w5 (p:aD ι) (q:ι → aD Ω) (X:Ω → α) :
    (p.joint q).Hf (fun v=>(v.1,X v.2)) = p.entropy+∑ i,p i*(q i).Hf X:=by
  let C:=ju X
  have he (r:aD Ω):r.Hf X = r.Hf C :=
    r.aZ X C (fun ω ν=>(gO X ω ν).symm)
  have he':(p.joint q).Hf (fun v=>(v.1,X v.2)) =
      (p.joint q).Hf (fun v=>(v.1,C v.2)):=by
    apply aZ
    intro v w
    simp only [Prod.mk.injEq,C,gO]
  rw [he',jW,H,A8,wZ]
  simp_rw [he,jW,H]
theorem WT (p:aD ι) (q:ι → aD Ω) (X:Ω → α) (Y:Ω → β) :
    (∑ i,p i*(q i).bT X Y) ≤ (p.mix q).bT X Y:=by
  have hm:=(p.joint q).u7 (fun v=>X v.2) (fun v=>Y v.2) Prod.fst
  have hid:(p.joint q).bT (fun v=>X v.2) (fun v=>(Y v.2,v.1)) =
      ∑ i,p i*(q i).bT X Y:=by
    unfold bT
    have h1:(p.joint q).Hf (fun v=>(X v.2,(Y v.2,v.1))) =
        (p.joint q).Hf (fun v=>(v.1,(X v.2,Y v.2))):=by
      apply aZ
      intro v w
      simp only [Prod.mk.injEq]
      tauto
    rw [h1,w5 p q (fun ω=>(X ω,Y ω)),
      kd (p.joint q) (fun v=>Y v.2) Prod.fst,w5]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rw [hid] at hm
  have he:=(p.joint q).vh Prod.snd X Y
  rw [qN] at he
  exact hm.trans_eq he.symm
theorem ow (p:aD ι) (q:ι → aD Ω) (f:ι → Ω → κ) :
    (p.joint q).map (fun v=>(v.1,f v.1 v.2)) = p.joint (fun i=>(q i).map (f i)):=by
  apply aD.ext; rintro ⟨i,x⟩
  simp only [f7,Fintype.sum_prod_type,jv,Prod.mk.injEq,ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp
theorem oL (p:aD ι) (q:ι → aD Ω) (X:ι → Ω → α) :
    (p.joint q).Hf (fun v=>(v.1,X v.1 v.2)) =
      p.entropy+∑ i,p i*(q i).Hf (X i):=by
  let C:=ju (fun v:ι × Ω=>X v.1 v.2)
  have he (i:ι):(q i).Hf (X i) = (q i).Hf (fun ω=>C (i,ω)):=by
    apply aZ
    intro ω ν
    exact (gO (fun v:ι × Ω=>X v.1 v.2) (i,ω) (i,ν)).symm
  have he':(p.joint q).Hf (fun v=>(v.1,X v.1 v.2)) =
      (p.joint q).Hf (fun v=>(v.1,C v)):=by
    apply aZ
    intro v w
    simp only [Prod.mk.injEq,C,gO]
  rw [he',jW,H,ow p q (fun i ω=>C (i,ω)),wZ]
  simp_rw [he,jW,H]
theorem Ka (p:aD ι) (q:ι → aD Ω)
    (X:ι → Ω → α) (Y:ι → Ω → β) :
    (∑ i,p i*(q i).bT (X i) (Y i)) ≤
      (p.joint q).bT (fun v=>X v.1 v.2) (fun v=>Y v.1 v.2):=by
  have hm:=(p.joint q).u7 (fun v=>X v.1 v.2) (fun v=>Y v.1 v.2) Prod.fst
  have hid:(p.joint q).bT (fun v=>X v.1 v.2) (fun v=>(Y v.1 v.2,v.1)) =
      ∑ i,p i*(q i).bT (X i) (Y i):=by
    unfold bT
    have h1:(p.joint q).Hf (fun v=>(X v.1 v.2,(Y v.1 v.2,v.1))) =
        (p.joint q).Hf (fun v=>(v.1,(X v.1 v.2,Y v.1 v.2))):=by
      apply aZ
      intro v w
      simp only [Prod.mk.injEq]
      tauto
    rw [h1,oL p q (fun i ω=>(X i ω,Y i ω)),
      kd (p.joint q) (fun v=>Y v.1 v.2) Prod.fst,oL]
    simp only [mul_sub,Finset.sum_sub_distrib]
    ring
  rwa [hid] at hm
theorem Je (p:aD Ω) (X:Ω → α) (c:β) :
    p.Hf (fun ω=>(X ω,c)) = p.Hf X:=by
  apply aZ
  intro ω ν
  simp
theorem Q7 (p:aD ι) (q:ι → aD Ω) (X:ι → Ω → α) :
    (∑ i,p i*(q i).Hf (X i)) ≤ (p.joint q).Hf (fun v=>X v.1 v.2):=by
  have h:=Ka p q X (fun _ _=>(0:ℕ))
  simpa only [bT,Ao,sub_zero,Je] using h
end aD
open scoped BigOperators Classical
noncomputable def aE.aV {Ω:Type bU} [Fintype Ω]
    (s:aE) (P:aD Ω) (Z:Ω → GaussianInt) (b:ℕ):ℝ :=
  P.gP (fun σ ω=>s.bC σ (Z ω)) b
noncomputable def aE.dV {Ω:Type bU} [Fintype Ω]
    (s:aE) (P:aD Ω) (X Y:Ω → GaussianInt)
    (b:ℕ) (hb:b < s.primes.card):ℝ :=
  𝔼 σ:Fin s.primes.card → Bool,𝔼 π:Equiv.Perm (Fin s.primes.card),
    P.bT (fun ω=>s.bC σ (X ω-Y ω) (π ⟨b,hb⟩))
      (fun ω=>(aD.aF (fun x=>s.bC σ (X x)) π b ω,
        aD.aF (fun x=>s.bC σ (Y x)) π b ω))
lemma aE.Jg {Ω:Type bU} {Κ:Type nW} [Fintype Ω] [Fintype Κ]
    (s:aE) (p:aD Ω) (f:Ω → Κ) (X Y:Κ → GaussianInt)
    (b:ℕ) (hb:b < s.primes.card) :
    s.dV (p.map f) X Y b hb = s.dV p (X ∘ f) (Y ∘ f) b hb:=by
  unfold aE.dV
  simp only [aD.vh,Function.comp_def]
  rfl
noncomputable def jh (z:ℕ → GaussianInt) (n:ℕ) :
    aD (Fin (n+1) × Fin (n+1)):=by
  let:=(jU z n).to_subtype
  exact (aD.uniform (differences (dK z n))).map (iz z n)
theorem Jh (s:aE) (z:ℕ → GaussianInt) (n:ℕ)
    {b r:ℕ} (hbr:b < r) (hr:r ≤ s.primes.card)
    {T R W d δ:ℝ} {e:ℂ} (he:‖e‖=1) (hT:5 ≤ T)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hW:1 ≤ W) (q8:W ≤ R) (hd:0 < d) (hd1:d < 1/4)
    (hδ:0 < δ) (jI:Real.log (R*W) ≤ (1-d)*(r*s.aP-δ))
    (cQ:1000 ≤ d^3*r)
    (hΔ:∀ x ∈ differences (dK z n),∀ y ∈ differences (dK z n),
      x-y ∈ gC e R W) :
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*
        Real.log (differences (dK z n)).card-2*b*Real.log (2*T) ≤
      (r-b:ℕ)*s.dV (jh z n)
        (fun ij=>z ij.1.val) (fun ij=>z ij.2.val) b (by omega):=by
  let Δ:=differences (dK z n)
  let hne:=jU z n
  let:=hne.to_subtype
  let X:Δ → GaussianInt:=fun ω=>z (iz z n ω).1.val
  let Y:Δ → GaussianInt:=fun ω=>z (iz z n ω).2.val
  have hXY:∀ ω,X ω-Y ω=ω:=kB z n
  have h:=s.Gk hbr hr Δ hne X Y hXY he hT hpT hW q8 hd hd1 hδ jI cQ hΔ
  change _ ≤ (r-b:ℕ)*s.dV
    ((aD.uniform Δ).map (iz z n))
      (fun ij=>z ij.1.val) (fun ij=>z ij.2.val) b (by omega)
  rw [s.Jg]
  change _ ≤ (r-b:ℕ)*s.dV (aD.uniform Δ) X Y b (by omega)
  simpa only [aE.dV,hXY] using h
theorem aE.A9 {ι:Type c9} {Ω:Type bU} [Fintype ι] [Fintype Ω]
    (s:aE) (p:aD ι) (q:ι → aD Ω)
    (X Y:ι → Ω → GaussianInt) {b:ℕ} (hb:b < s.primes.card) :
    (∑ i,p i*s.dV (q i) (X i) (Y i) b hb) ≤
      s.dV (p.joint q) (fun v=>X v.1 v.2) (fun v=>Y v.1 v.2) b hb:=by
  have h:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s:=Finset.univ) (fun π _ =>
      p.Ka q (fun i ω=>s.bC σ (X i ω-Y i ω) (π ⟨b,hb⟩))
        (fun i ω=>(aD.aF (fun x=>s.bC σ (X i x)) π b ω,
          aD.aF (fun x=>s.bC σ (Y i x)) π b ω))))
  simpa only [aE.dV,Finset.expect_sum_comm,Finset.mul_expect] using! h
lemma w6 {Ω:Type bU} [Fintype Ω] (s:aE)
    (p:aD Ω) (X Y:Ω → GaussianInt) (b:ℕ) :
    s.aV p X b+s.aV p Y b ≤
      2*s.aV ((aD.uniform Bool).joint (fun _=>p))
        (fun v=>if v.1 then X v.2 else Y v.2) b:=by
  have h:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s:=Finset.univ) (fun π _ =>
      (aD.uniform Bool).Q7 (fun _=>p)
        (fun c ω=>aD.aF (fun x=>s.bC σ (if c then X x else Y x)) π b ω)))
  simp only [Fintype.sum_bool,aD.m4,Fintype.card_bool,Nat.cast_ofNat,
    Bool.false_eq_true,ite_false,ite_true,Finset.expect_add_distrib,← Finset.mul_expect] at h
  change (2:ℝ)⁻¹*s.aV p X b+(2:ℝ)⁻¹*s.aV p Y b ≤
    s.aV ((aD.uniform Bool).joint (fun _=>p))
      (fun v=>if v.1 then X v.2 else Y v.2) b at h
  linarith
theorem aE.vZ {Ω:Type bU} [Fintype Ω]
    (s:aE) (p:aD Ω) (X Y Z:Ω → GaussianInt)
    {b q:ℕ} (hb:0 < b) (hbq:b < q) (hq:q ≤ s.primes.card) :
    (b:ℝ)*((q-b:ℕ)*s.dV p X Y b (by omega)+
      s.aV p Z q-p.Hf (fun ω=>X ω-Y ω)-p.Hf (fun ω=>X ω-Z ω)) ≤
      (q:ℝ)*(s.aV p X b+s.aV p Y b):=by
  have h (σ:Fin s.primes.card → Bool):=p.tw
    (fun ω=>s.bC σ (X ω)) (fun ω=>s.bC σ (Y ω))
    (fun ω=>s.bC σ (Z ω)) (fun ω=>s.bC σ (X ω-Y ω))
    (fun ω=>X ω-Y ω) (fun ω=>X ω-Z ω) hb hbq hq
    (by intro i ω ν hx hy; exact kR hx hy)
    (by
      intro i ω ν hx hd
      have h:=kR hx hd
      simpa only [sub_sub_cancel,aE.bC] using h)
    (by intro i ω ν hh; rw [hh])
    (by
      intro i ω ν hx he
      have h:=kR hx (congrArg (aR _) he)
      simpa only [sub_sub_cancel,aE.bC] using h)
  have hh:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _=>h σ)
  simpa only [aE.aV,aD.gP,aE.dV,
    Finset.expect_sub_distrib,Finset.expect_add_distrib,← Finset.mul_expect,Fintype.expect_const] using hh
theorem aE.Ld {Ω:Type bU} [Fintype Ω]
    (s:aE) (p:aD Ω) (X Y Z:Ω → GaussianInt)
    {b q:ℕ} (hb:0 < b) (hbq:b < q) (hq:q ≤ s.primes.card)
    {F R:ℝ} (hF:F ≤ s.dV p X Y b (by omega))
    (hR:1 ≤ R) (hXY:∀ ω,‖((X ω-Y ω:GaussianInt):ℂ)‖ ≤ R)
    (hXZ:∀ ω,‖((X ω-Z ω:GaussianInt):ℂ)‖ ≤ R) :
    (b:ℝ)*((q-b:ℕ)*F+s.aV p Z q-2*(Real.log 36+2*Real.log R)) ≤
      2*(q:ℝ)*s.aV ((aD.uniform Bool).joint (fun _=>p))
        (fun v=>if v.1 then X v.2 else Y v.2) b:=by
  have hc:=s.vZ p X Y Z hb hbq hq
  have h1:=je p (fun ω=>X ω-Y ω) hR hXY
  have h2:=je p (fun ω=>X ω-Z ω) hR hXZ
  have he:=w6 s p X Y b
  have hm:=mul_le_mul_of_nonneg_left he (Nat.cast_nonneg q)
  have hf:=mul_le_mul_of_nonneg_left hF (show (0:ℝ) ≤ (q-b:ℕ) by positivity)
  have hsub:(q-b:ℕ)*F+s.aV p Z q-2*(Real.log 36+2*Real.log R) ≤
      (q-b:ℕ)*s.dV p X Y b (by omega)+s.aV p Z q-
        p.Hf (fun ω=>X ω-Y ω)-p.Hf (fun ω=>X ω-Z ω):=by linarith
  have hmul:=mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg b)
  nlinarith
open scoped BigOperators Classical
lemma Kd {g L r:ℝ} (hg:0 < g) (hg1:g ≤ 1/100)
    (hL:1 ≤ L) (hr:0 < r) (cQ:5120 ≤ g^4*r) :
    r*(Real.log 2)^2/(2*g*r*L)^2 ≤ g ∧ Real.exp (-(g^3*r/5120)) ≤ g:=by
  have hlog:0 ≤ Real.log 2:=Real.log_nonneg (by norm_num)
  have Ze:Real.log 2 ≤ 1:=by
    have h:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    linarith
  have hl2:(Real.log 2)^2 ≤ 1:=by nlinarith
  have hg4:0 < g^4:=pow_pos hg _
  have hg3:0 < g^3:=pow_pos hg _
  have hgL:0 < 2*g*r*L:=by positivity
  have hgr:1 ≤ g^3*r:=by
    have h:g^4*r = g*(g^3*r):=by ring
    have hp:0 ≤ g^3*r:=mul_nonneg hg3.le hr.le
    nlinarith
  have SM:1 ≤ L^2:=by nlinarith
  have hprod:=mul_le_mul hgr SM (by norm_num:(0:ℝ)≤1) (mul_nonneg hg3.le hr.le)
  have hrr:0 ≤ r*(4*(g^3*r*L^2)-1):=mul_nonneg hr.le (by nlinarith)
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hgL)).mpr
    have h:=mul_le_mul_of_nonneg_left hl2 hr.le
    nlinarith
  · have hpow:1/g ≤ g^3*r/5120:=by
      apply (div_le_iff₀ hg).mpr
      nlinarith
    have Zi : -(1/g) ≤ Real.log g:=by
      have h:=Real.log_le_sub_one_of_pos (inv_pos.mpr hg)
      rw [Real.log_inv] at h
      simp only [one_div] at h ⊢
      linarith
    exact (Real.exp_le_exp.mpr (by linarith : -(g^3*r/5120) ≤ Real.log g)).trans_eq
      (Real.exp_log hg)
lemma NR {g a L r:ℝ} (hg:0 < g) (hg1:g ≤ 1/100)
    (ha:0 ≤ a) (kT:(1+10*g)*a ≤ r*L) :
    a ≤ (1-g)*(r*L-2*g*r*L):=by
  have hfac:0 ≤ (1-g)*(1-2*g):=mul_nonneg (by linarith) (by linarith)
  have h:=mul_le_mul_of_nonneg_left kT hfac
  have hn:0 ≤ g*(7-30*g):=mul_nonneg hg.le (by linarith)
  have he:1 ≤ (1-g)*(1-2*g)*(1+10*g):=by
    have hg3:0 ≤ g^3:=pow_nonneg hg.le _
    nlinarith
  have ha':=mul_le_mul_of_nonneg_right he ha
  nlinarith
theorem aE.zF (s:aE)
    (z:ℕ → GaussianInt) (n:ℕ) {b r:ℕ}
    (hbr:b < r) (hr:r ≤ s.primes.card)
    {T R W g a:ℝ} {e:ℂ} (he:‖e‖=1) (hT:5 ≤ T)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hW:1 ≤ W) (q8:W ≤ R) (hg:0 < g) (hg1:g ≤ 1/100)
    (jE:1 ≤ s.aP) (ha:a = Real.log (R*W)) (ha0:0 ≤ a)
    (kT:(1+10*g)*a ≤ r*s.aP) (Gh:r*s.aP ≤ (1+11*g)*a)
    (cQ:5120 ≤ g^4*r)
    (hsize:(1-g)*a ≤ Real.log (differences (dK z n)).card)
    (jz:2*b*Real.log (2*T) ≤ 8*g*a)
    (hΔ:∀ x ∈ differences (dK z n),∀ y ∈ differences (dK z n),
      x-y ∈ gC e R W) :
    (1-30*g)*s.aP ≤ s.dV (jh z n)
      (fun ij=>z ij.1.val) (fun ij=>z ij.2.val) b (by omega):=by
  have hr0:(0:ℝ) < r:=by exact_mod_cast (show 0 < r by omega)
  have XP:g < 1/4:=by linarith
  have hδ:0 < 2*g*r*s.aP:=by positivity
  have jI:Real.log (R*W) ≤ (1-g)*(r*s.aP-2*g*r*s.aP):=by
    rw [← ha]
    exact NR hg hg1 ha0 kT
  have U9:1000 ≤ g^3*(r:ℝ):=by
    have hp:0 ≤ g^3*(r:ℝ):=by positivity
    have hid:g^4*(r:ℝ) = g*(g^3*r):=by ring
    nlinarith
  have iJ:=Kd hg hg1 jE hr0 cQ
  have h:=Jh s z n hbr hr he hT hpT hW q8 hg XP hδ
    jI U9 hΔ
  have VZ:0 ≤ Real.log (differences (dK z n)).card:=by
    have hh:0 ≤ (1-g)*a:=mul_nonneg (by linarith) ha0
    linarith
  have he:=mul_le_mul_of_nonneg_right (show 1-2*g ≤
      1-(r:ℝ)*(Real.log 2)^2/(2*g*r*s.aP)^2-
        Real.exp (-(g^3*r/5120)) by linarith [iJ.1,iJ.2]) VZ
  have hs:=mul_le_mul_of_nonneg_left hsize (show 0 ≤ 1-2*g by linarith)
  have hnum:(1-11*g)*a ≤ (r-b:ℕ)*s.dV (jh z n)
      (fun ij=>z ij.1.val) (fun ij=>z ij.2.val) b (by omega):=by
    have hx:0 ≤ 2*g^2*a:=by positivity
    nlinarith
  have hp0:0 ≤ 1-30*g:=by linarith
  have hh:=mul_le_mul_of_nonneg_left Gh hp0
  have hh2:(1-30*g)*((1+11*g)*a) ≤ (1-11*g)*a:=by
    have h1:0 ≤ g*a:=mul_nonneg hg.le ha0
    have h2:0 ≤ g^2*a:=mul_nonneg (sq_nonneg _) ha0
    nlinarith
  have XQ:(r-b:ℕ) ≤ (r:ℝ):=by exact_mod_cast Nat.sub_le r b
  have hb0:(0:ℝ) < (r-b:ℕ):=by exact_mod_cast Nat.sub_pos_of_lt hbr
  have hm:=mul_le_mul_of_nonneg_right XQ (mul_nonneg hp0 (by linarith:0 ≤ s.aP))
  nlinarith
lemma aE.m5 (s:aE) (hne:s.primes.Nonempty) {T:ℝ}
    (hT:0 < T) (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T) :
    Real.log T ≤ s.aP ∧ s.aP ≤ Real.log (2*T):=by
  have:Nonempty (Fin s.primes.card):=Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hne)
  constructor
  · have h:=Finset.expect_le_expect (s:=Finset.univ) (fun i _ =>
      Real.log_le_log hT (hpT _ (s.enumeration i).property).1)
    simpa only [aE.aP,Fintype.expect_const] using h
  · apply Finset.expect_le (Finset.univ_nonempty)
    intro i _
    exact Real.log_le_log (lt_of_lt_of_le hT (hpT _ (s.enumeration i).property).1)
      (hpT _ (s.enumeration i).property).2
theorem aE.Mt (s:aE) (hne:s.primes.Nonempty)
    (z:ℕ → GaussianInt) {n:ℕ} (hn:1 ≤ n) (hinj:Function.Injective z)
    {D T g:ℝ} (hD:1 ≤ D) (hT:5 ≤ T)
    (hz:∀ i < n,dist (z i:ℂ) (z (i+1):ℂ) ≤ D)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg:0 < g) (hg1:g ≤ 1/100) (hL:1 ≤ s.aP)
    {b:ℕ} (hu:0 < Real.log n-Real.log 18)
    (V0:s.aP ≤ g*(Real.log n-Real.log 18))
    (cQ:5120*s.aP ≤ g^4*(Real.log n-Real.log 18))
    (jz:(b:ℝ)*s.aP ≤ g*(Real.log n-Real.log 18))
    (hsize:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ)) ≤
      g*(Real.log n-Real.log 18))
    (hcap:2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*s.aP) :
    ∃ hb:b < s.primes.card,
      (1-30*g)*s.aP ≤ s.dV (jh z n)
        (fun ij=>z ij.1.val) (fun ij=>z ij.2.val) b hb:=by
  obtain ⟨R,W,e,c,hW,q8,he,Qj,hnA,XR,YN⟩ :=
    Et z hn hinj hD hz
  have hRp:0 < R:=by linarith
  have hWp:0 < W:=by linarith
  have hA:0 < R*W:=mul_pos hRp hWp
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn
  have hLp:0 < s.aP:=by linarith
  let a:=Real.log (16*(R*W))
  let u:=Real.log n-Real.log 18
  have hua:u ≤ a:=by
    have h:=Real.log_le_log hnR hnA
    rw [Real.log_mul (by norm_num:(18:ℝ)≠0) hA.ne'] at h
    have TD:0 ≤ Real.log 16:=Real.log_nonneg (by norm_num)
    dsimp [u,a]
    rw [Real.log_mul (by norm_num:(16:ℝ)≠0) hA.ne']
    linarith
  have ha0:0 < a:=lt_of_lt_of_le hu hua
  have hav:a ≤ 2*Real.log n+Real.log 16+2*Real.log D:=by
    have h:=Real.log_le_log hA XR
    rw [Real.log_mul (pow_ne_zero _ (by linarith:D≠0)) (pow_ne_zero _ hnR.ne'),
      Real.log_pow,Real.log_pow] at h
    dsimp [a]
    rw [Real.log_mul (by norm_num:(16:ℝ)≠0) hA.ne']
    norm_num at h
    linarith only [h]
  let r:=⌈(1+10*g)*a/s.aP⌉₊
  have hlo:(1+10*g)*a ≤ (r:ℝ)*s.aP:=by
    exact (div_le_iff₀ hLp).mp (Nat.le_ceil _)
  have hhi:(r:ℝ)*s.aP ≤ (1+11*g)*a:=by
    have hx:0 ≤ (1+10*g)*a/s.aP:=by positivity
    have hc:=Nat.ceil_lt_add_one hx
    have hh:=mul_lt_mul_of_pos_right hc hLp
    have heq:((1+10*g)*a/s.aP+1)*s.aP = (1+10*g)*a+s.aP:=by
      rw [add_mul,div_mul_cancel₀ _ hLp.ne',one_mul]
    rw [heq] at hh
    have hgu:=mul_le_mul_of_nonneg_left hua hg.le
    change (r:ℝ)*s.aP < (1+10*g)*a+s.aP at hh
    nlinarith only [hh,V0,hgu]
  have hr:r ≤ s.primes.card:=by
    suffices hh:(r:ℝ) ≤ s.primes.card by exact_mod_cast hh
    have hh:(1+11*g)*a ≤ 2*a:=by nlinarith only [hg1,ha0]
    nlinarith only [hhi,hh,hav,hcap,hLp]
  have hbr:b < r:=by
    suffices hh:(b:ℝ) < r by exact_mod_cast hh
    have hgu:=mul_le_mul_of_nonneg_left hua hg.le
    nlinarith only [jz,hgu,hlo,hg1,hLp,ha0]
  have hlr:5120 ≤ g^4*(r:ℝ):=by
    have hg4:0 < g^4:=pow_pos hg _
    have h1:u ≤ (r:ℝ)*s.aP:=by nlinarith only [hlo,hua,hg,ha0]
    have h2:=mul_le_mul_of_nonneg_left h1 hg4.le
    nlinarith only [h2,cQ,hLp]
  have hC:0 < max D ((bY (4*D)).card:ℝ):=lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hdc:(0:ℝ) < (differences (dK z n)).card:=by
    exact_mod_cast Finset.card_pos.mpr (jU z n)
  have hsz:(1-g)*a ≤ Real.log (differences (dK z n)).card:=by
    have h:=Real.log_le_log hA YN
    rw [Real.log_mul hC.ne' hdc.ne'] at h
    have hgu:=mul_le_mul_of_nonneg_left hua hg.le
    have XS:a = Real.log 16+Real.log (R*W):=by
      exact Real.log_mul (by norm_num) hA.ne'
    nlinarith only [h,hgu,XS,hsize]
  have vG:Real.log (2*T) ≤ 2*s.aP:=by
    have hm:=s.m5 hne (by linarith) hpT
    have vG:Real.log 2 ≤ 1:=by
      have h:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
      linarith
    rw [Real.log_mul (by norm_num:(2:ℝ)≠0) (by linarith:T≠0)]
    linarith only [hm.1,vG,hL]
  have hbc:2*(b:ℝ)*Real.log (2*T) ≤ 8*g*a:=by
    have h:=mul_le_mul_of_nonneg_left vG (by positivity:(0:ℝ)≤2*b)
    have hgu:=mul_le_mul_of_nonneg_left hua hg.le
    have hga:0 ≤ g*a:=by positivity
    nlinarith only [h,hgu,jz,hga]
  refine ⟨by omega,?_⟩
  apply s.zF z n hbr hr (e:=star e) (R:=4*R) (W:=4*W)
    (by simpa using he) hT hpT (by linarith) (by linarith) hg hg1 hL
    (a:=a) (by dsimp [a]; congr 1; ring) ha0.le hlo hhi hlr hsz hbc
  exact EK (dK z n) Qj
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU nW cD dD g4 c9
namespace GaussianMoat
section
open scoped BigOperators Classical
structure bR where
  last:ℕ
  law:aD (Fin (last+1))
noncomputable def r9 (a n:ℕ) :
    Bool × (Fin (a+1) × (Fin (n+1) × Fin (n+1))) → Fin (a+n+1) :=
  fun v=>⟨v.2.1.val+(if v.1 then v.2.2.1.val else v.2.2.2.val),by
    split_ifs <;> omega⟩
noncomputable def bR.step (P:bR) (z:ℕ → GaussianInt) (n:ℕ):bR where
  last:=P.last+n
  law:=((aD.uniform Bool).joint (fun _=>P.law.joint (fun a =>
    jh (fun t=>z (a.val+t)) n))).map (r9 P.last n)
lemma aE.lG {Ω:Type bU} {Κ:Type nW} [Fintype Ω] [Fintype Κ]
    (s:aE) (p:aD Ω) (f:Ω → Κ) (Z:Κ → GaussianInt) (b:ℕ) :
    s.aV (p.map f) Z b = s.aV p (Z ∘ f) b:=by
  unfold aV aD.gP aD.bF
  simp only [aD.NG]
  rfl
lemma aE.jQ {Ω:Type bU} {Κ:Type nW} [Fintype Ω] [Fintype Κ]
    (s:aE) (p:aD Ω) (q:Ω → aD Κ) (Z:Ω → GaussianInt) (b:ℕ) :
    s.aV (p.joint q) (fun v=>Z v.1) b = s.aV p Z b:=by
  have h:=s.lG (p.joint q) Prod.fst Z b
  rw [aD.qM] at h
  exact h.symm
lemma DB (z:ℕ → GaussianInt) (hz:Function.Injective z) (a:ℕ) :
    Function.Injective (fun t=>z (a+t)):=by intro i j h; have:=hz h; omega
lemma g8 (z:ℕ → GaussianInt) {D:ℝ} (hD:0 ≤ D)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (a n i j:ℕ)
    (hi:i ≤ n) (hj:j ≤ n) :
    ‖((z (a+i)-z (a+j):GaussianInt):ℂ)‖ ≤ D*n:=by
  have h:=tP (fun t=>z (a+t)) hD
    (fun t _=>by simpa only [Nat.add_assoc] using hstep (a+t)) hi hj
  simpa only [dist_eq_norm,map_sub] using h
theorem bR.NU (P:bR) (s:aE)
    (z:ℕ → GaussianInt) {D F:ℝ} (hD:1 ≤ D)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q:ℕ}
    (hn:1 ≤ n) (hb:0 < b) (hbq:b < q) (hq:q ≤ s.primes.card)
    (hF:∀ a:Fin (P.last+1),F ≤ s.dV
      (jh (fun t=>z (a.val+t)) n)
      (fun ij=>z (a.val+ij.1.val)) (fun ij=>z (a.val+ij.2.val)) b (by omega)) :
    (b:ℝ)*((q-b:ℕ)*F+s.aV P.law (fun a=>z a.val) q-
      2*(Real.log 36+2*Real.log (D*n))) ≤
      2*(q:ℝ)*s.aV (P.step z n).law (fun a=>z a.val) b:=by
  let K:=P.law.joint (fun a=>jh (fun t=>z (a.val+t)) n)
  let X:=fun v:Fin (P.last+1) × (Fin (n+1) × Fin (n+1))=>z (v.1.val+v.2.1.val)
  let Y:=fun v:Fin (P.last+1) × (Fin (n+1) × Fin (n+1))=>z (v.1.val+v.2.2.val)
  let Z:=fun v:Fin (P.last+1) × (Fin (n+1) × Fin (n+1))=>z v.1.val
  have hF':F ≤ s.dV K X Y b (by omega):=by
    have hh:=s.A9 P.law
      (fun a=>jh (fun t=>z (a.val+t)) n)
      (fun a ij=>z (a.val+ij.1.val)) (fun a ij=>z (a.val+ij.2.val)) (by omega:b < s.primes.card)
    apply le_trans _ hh
    have hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun a _ =>
      mul_le_mul_of_nonneg_left (hF a) (P.law.nonneg a))
    simpa only [← Finset.sum_mul,P.law.dN,one_mul] using hsum
  have V5:1 ≤ D*n:=one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hn)
  have h:=s.Ld K X Y Z hb hbq hq hF' V5
    (fun v=>g8 z (by linarith) hstep _ _ _ _ (by omega) (by omega))
    (fun v=>by
      change ‖((z (v.1.val+v.2.1.val)-z v.1.val:GaussianInt):ℂ)‖ ≤ D*n
      simpa only [Nat.add_zero] using
        g8 z (by linarith) hstep v.1.val n v.2.1.val 0 (by omega) (by omega))
  have hZ:=s.jQ P.law
    (fun a=>jh (fun t=>z (a.val+t)) n) (fun a=>z a.val) q
  rw [hZ] at h
  have hout:s.aV (P.step z n).law (fun a=>z a.val) b =
      s.aV ((aD.uniform Bool).joint (fun _=>K))
        (fun v=>if v.1 then X v.2 else Y v.2) b:=by
    change s.aV (((aD.uniform Bool).joint (fun _=>K)).map
      (r9 P.last n)) (fun a=>z a.val) b = _
    rw [s.lG]
    apply congrArg (fun F=>s.aV ((aD.uniform Bool).joint (fun _=>K)) F b)
    funext v
    simp only [Function.comp_def,r9,X,Y]
    split_ifs <;> rfl
  rw [hout]
  exact h
end
namespace aD
section
open scoped BigOperators Classical
variable {Ω:Type bU} [Fintype Ω]
noncomputable def prob (p:aD Ω) (E:Ω → Prop):ℝ:=∑ ω,if E ω then p ω else 0
lemma nZ (p:aD Ω) (E:Ω → Prop):0 ≤ p.prob E:=by
  exact Finset.sum_nonneg (fun ω _=>by split_ifs <;> simp [p.nonneg ω])
lemma prob_le_one (p:aD Ω) (E:Ω → Prop):p.prob E ≤ 1:=by
  rw [← p.dN]
  exact Finset.sum_le_sum (fun ω _=>by split_ifs <;> simp [p.nonneg ω])
lemma v7 (p:aD Ω) {E F:Ω → Prop} (h:∀ ω,E ω → F ω) :
    p.prob E ≤ p.prob F:=by
  apply Finset.sum_le_sum
  intro ω _
  by_cases he:E ω
  · simp [he,h ω he]
  · by_cases hf:F ω <;> simp [he,hf,p.nonneg ω]
noncomputable def f6 (p:aD Ω) (n:ℕ):aD (Fin n → Ω) where
  mass:=fun x=>∏ i,p (x i)
  nonneg:=fun x=>Finset.prod_nonneg (fun i _=>p.nonneg _)
  dN:=by
    rw [← Fintype.prod_sum]
    simp only [p.dN,Finset.prod_const_one]
@[simp] lemma Mv (p:aD Ω) (n:ℕ) (x:Fin n → Ω) :
    p.f6 n x = ∏ i,p (x i):=rfl
lemma Q8 (p:aD Ω) (n:ℕ) (f:Ω → ℝ) :
    (∑ x:Fin n → Ω,p.f6 n x * ∏ i,f (x i)) = (∑ ω,p ω*f ω)^n:=by
  simp only [Mv,← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun ω=>p ω*f ω) n).symm
lemma Gm {t:ℝ} (ht:0 ≤ t):Real.exp (-t) ≤ 1-t+t^2/2:=by
  have hm:Monotone (fun x:ℝ=>1-x+x^2/2-Real.exp (-x)):=by
    apply monotone_of_hasDerivAt_nonneg (f':=fun x => -1+x+Real.exp (-x))
    · intro x
      convert! (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
          (((hasDerivAt_id x).neg).exp) using 1
      simp only [Pi.neg_apply,id_eq]
      ring
    · intro x
      have h:=Real.add_one_le_exp (-x)
      change 0 ≤ -1+x+Real.exp (-x)
      linarith
  have h:=hm ht
  simpa using h
lemma Kh (p:aD Ω) (S:Ω → ℝ) {t a:ℝ} (ht:0 ≤ t) :
    p.prob (fun ω=>S ω ≤ a) ≤ Real.exp (t*a) * ∑ ω,p ω*Real.exp (-t*S ω):=by
  have h (ω:Ω):(if S ω ≤ a then p ω else 0) ≤
      Real.exp (t*a)*(p ω*Real.exp (-t*S ω)):=by
    by_cases hh:S ω ≤ a
    · rw [dO hh]
      have he:1 ≤ Real.exp (t*a+-t*S ω):=Real.one_le_exp_iff.mpr (by nlinarith)
      calc
        p ω = p ω*1:=by ring
        _ ≤ p ω*Real.exp (t*a+-t*S ω):=mul_le_mul_of_nonneg_left he (p.nonneg ω)
        _ = Real.exp (t*a)*(p ω*Real.exp (-t*S ω)):=by rw [Real.exp_add]; ring
    · rw [gR hh]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  simpa only [prob,Finset.mul_sum] using Finset.sum_le_sum (s:=Finset.univ) (fun ω _=>h ω)
lemma Bc (p:aD Ω) (E:Ω → Prop) (t:ℝ) :
    (∑ ω,p ω*Real.exp (-t*(if E ω then 1 else 0))) =
      1+p.prob E*(Real.exp (-t)-1):=by
  have he (ω:Ω):p ω*Real.exp (-t*(if E ω then 1 else 0)) =
      p ω+(if E ω then p ω else 0)*(Real.exp (-t)-1):=by
    split_ifs <;> simp only [mul_one,mul_zero,Real.exp_zero,zero_mul,add_zero]
    ring
  simp only [he,Finset.sum_add_distrib,← Finset.sum_mul,p.dN,prob]
theorem OD (p:aD Ω) (E:Ω → Prop) (n:ℕ)
    {μ δ:ℝ} (hμ:0 < μ) (hδ:0 ≤ δ) (hp:μ ≤ p.prob E) :
    (p.f6 n).prob (fun x=>(∑ i:Fin n,if E (x i) then (1:ℝ) else 0) ≤ n*(μ-δ)) ≤
      Real.exp (- (n:ℝ)*δ^2/(2*μ)):=by
  let t:=δ/μ
  have ht:0 ≤ t:=div_nonneg hδ hμ.le
  have hm:=Kh (p.f6 n)
    (fun x=>∑ i:Fin n,if E (x i) then (1:ℝ) else 0) ht (a:=n*(μ-δ))
  have uO:(∑ x:Fin n → Ω,p.f6 n x *
      Real.exp (-t*∑ i:Fin n,if E (x i) then 1 else 0)) =
      (1+p.prob E*(Real.exp (-t)-1))^n:=by
    simp_rw [Finset.mul_sum,Real.exp_sum]
    rw [Q8 p n (fun ω=>Real.exp (-t*(if E ω then 1 else 0))),Bc]
  rw [uO] at hm
  have V6:0 ≤ 1+p.prob E*(Real.exp (-t)-1):=by
    rw [← Bc]
    exact Finset.sum_nonneg (fun ω _=>mul_nonneg (p.nonneg ω) (Real.exp_pos _).le)
  have hbase:1+p.prob E*(Real.exp (-t)-1) ≤ Real.exp (μ*(Real.exp (-t)-1)):=by
    have hn:Real.exp (-t)-1 ≤ 0:=by
      have h:=Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      linarith
    have h1:=mul_le_mul_of_nonpos_right hp hn
    have h2:=Real.add_one_le_exp (μ*(Real.exp (-t)-1))
    linarith
  have hpw:=pow_le_pow_left₀ V6 hbase n
  have hmul:=mul_le_mul_of_nonneg_left hpw (Real.exp_pos (t*(n*(μ-δ)))).le
  apply hm.trans (hmul.trans ?_)
  rw [← Real.exp_nat_mul,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he:=Gm ht
  have h:=mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg n) hμ.le)
  have hid:t*((n:ℝ)*(μ-δ))+(n:ℝ)*μ*(-t+t^2/2) = -(n:ℝ)*δ^2/(2*μ):=by
    dsimp [t]
    field_simp
    ring
  rw [← hid]
  nlinarith
end
section
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
lemma le_map_apply (p:aD Ω) (X:Ω → α) (ω:Ω):p ω ≤ p.map X (X ω):=by
  have h:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun ν=>if X ν=X ω then p ν else 0)
    (fun ν _=>by split_ifs <;> simp [p.nonneg ν]) (Finset.mem_univ ω)
  simpa only [ite_true,f7] using h
noncomputable def eO (p:aD Ω) (X:Ω → α) (a:α):aD Ω :=
  if h:p.map X a = 0 then p else {
    mass:=fun ω=>if X ω=a then p ω/(p.map X a) else 0
    nonneg:=fun ω=>by split_ifs; exact div_nonneg (p.nonneg ω) ((p.map X).nonneg a); rfl
    dN:=by
      have he:(∑ ω,if X ω=a then p ω/(p.map X a) else 0) =
          (∑ ω,if X ω=a then p ω else 0)/(p.map X a):=by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp
      rw [he,← f7,div_self h] }
lemma oM (p:aD Ω) (X:Ω → α) (a:α) (ω:Ω) :
    p.map X a * p.eO X a ω = if X ω=a then p ω else 0:=by
  by_cases hz:p.map X a=0
  · rw [hz,zero_mul]
    split_ifs with hh
    · have h:=p.le_map_apply X ω
      rw [hh,hz] at h
      exact (le_antisymm h (p.nonneg ω)).symm
    · rfl
  · unfold eO
    rw [O7 hz]
    change p.map X a * (if X ω=a then p ω/(p.map X a) else 0) = _
    by_cases hx:X ω=a
    · rw [dO hx,dO hx]
      exact mul_div_cancel₀ _ hz
    · rw [gR hx,gR hx,mul_zero]
lemma disintegration (p:aD Ω) (X:Ω → α) :
    (p.map X).joint (p.eO X) = p.map (fun ω=>(X ω,ω)):=by
  apply aD.ext; rintro ⟨a,ω⟩
  rw [jv,oM,f7]
  simp only [Prod.mk.injEq]
  rw [Finset.sum_eq_single ω]
  · simp
  · intro ν _ hn
    simp [hn]
  · simp
lemma Sm (p:aD Ω) (X:Ω → α) :
    (p.map X).mix (p.eO X) = p:=by
  rw [← qN,disintegration,map_comp]
  exact p.map_id
lemma B9 (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.H (fun ω=>(X ω,Y ω)) = p.H X+∑ a,p.map X a*(p.eO X a).H Y:=by
  have h:=(p.map X).w5 (p.eO X) Y
  rw [disintegration,NG] at h
  simpa only [jW,H,Function.comp_def] using h
lemma Gp (p:aD Ω) (Y:Ω → β) (X:Ω → α) :
    p.g7 Y X = ∑ a,p.map X a*(p.eO X a).H Y:=by
  unfold g7
  rw [p.Dt Y X,p.B9 X Y]
  ring
lemma oN (p:aD Ω) (f:Ω → α) (E:α → Prop) :
    (p.map f).prob E = p.prob (fun ω=>E (f ω)):=by
  simp only [prob,f7]
  have h (a:α):(if E a then ∑ ω,if f ω=a then p ω else 0 else 0) =
      ∑ ω,if f ω=a then (if E a then p ω else 0) else 0:=by
    by_cases he:E a <;> simp [he]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp
lemma pH (p:aD Ω) (q:Ω → aD α) (E:Ω × α → Prop) :
    (p.joint q).prob E = ∑ ω,p ω*(q ω).prob (fun a=>E (ω,a)):=by
  simp only [prob,Fintype.sum_prod_type,jv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp
lemma Mw (p:aD Ω) (X:Ω → α) (E:Ω → Prop) :
    (∑ a,p.map X a*(p.eO X a).prob E) = p.prob E:=by
  rw [← pH (p.map X) (p.eO X) (fun v=>E v.2),disintegration,oN]
lemma v8 (p:aD Ω) (f:Ω → ℝ) (hf:∀ ω,0 ≤ f ω)
    {a:ℝ} (ha:0 < a) :
    p.prob (fun ω=>a < f ω) ≤ (∑ ω,p ω*f ω)/a:=by
  apply (le_div_iff₀ ha).mpr
  rw [prob,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh:a < f ω
  · simp only [dO hh]
    exact mul_le_mul_of_nonneg_left hh.le (p.nonneg ω)
  · simp only [gR hh,zero_mul]
    exact mul_nonneg (p.nonneg ω) (hf ω)
lemma pI (p:aD Ω) (E:Ω → Prop) :
    p.prob (fun ω=>¬ E ω) = 1-p.prob E:=by
  have h:p.prob (fun ω=>¬ E ω)+p.prob E = 1:=by
    rw [prob,prob,← Finset.sum_add_distrib,← p.dN]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases he:E ω <;> simp [he]
  linarith
lemma Ip (p:aD Ω) (E F:Ω → Prop) :
    p.prob E-p.prob (fun ω=>¬ F ω) ≤ p.prob (fun ω=>E ω ∧ F ω):=by
  rw [prob,prob,prob,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases he:E ω <;> by_cases hf:F ω <;> simp [he,hf,p.nonneg ω]
lemma Kj {ι:Type c9} [Fintype ι] (p:aD Ω) (E:ι → Ω → Prop) :
    p.prob (fun ω=>∃ i,E i ω) ≤ ∑ i,p.prob (E i):=by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hh:∃ i,E i ω
  · obtain ⟨i,hi⟩:=hh
    rw [dO ⟨i,hi⟩]
    have h:=Finset.single_le_sum (s:=Finset.univ)
      (f:=fun i=>if E i ω then p ω else 0)
      (fun j _=>by split_ifs <;> simp [p.nonneg ω]) (Finset.mem_univ i)
    simpa only [dO hi] using h
  · simp only [gR hh]
    exact Finset.sum_nonneg (fun i _=>by split_ifs <;> simp [p.nonneg ω])
end
open scoped BigOperators Classical
variable {Ω:Type bU} {Κ:Type nW} {ι:Type c9} {α:Type cD} {β:Type dD} [Fintype Ω] [Fintype Κ] [Fintype ι]
lemma lA (p:aD Ω) (e:Ω ≃ Κ) (x:Κ) :
    p.map e x = p (e.symm x):=by
  rw [f7,Finset.sum_eq_single (e.symm x)]
  · simp
  · intro ω _ hn
    have hh:e ω ≠ x:=by intro h; exact hn (e.injective (by simpa using h))
    simp [hh]
  · simp
lemma Lg (p:aD Ω) (e:Ω ≃ Κ) :
    (p.map e).entropy = p.entropy:=by
  simp only [entropy,eo,lA]
  exact e.symm.sum_comp (fun ω=>Real.negMulLog (p ω))
lemma TJ (p:aD Ω) (n:ℕ) :
    p.f6 (n+1) = (p.joint (fun _=>p.f6 n)).map
      (Fin.consEquiv (fun _:Fin (n+1)=>Ω)):=by
  apply aD.ext; rintro x
  rw [lA]
  change (∏ i:Fin (n+1),p (x i)) = p (x 0)*(∏ i:Fin n,p (x i.succ))
  exact Fin.prod_univ_succ _
lemma Ra (p:aD Ω) (n:ℕ) :
    (p.f6 n).entropy = n*p.entropy:=by
  induction n with
  | zero =>
    have he:p.f6 0 = uniform (Fin 0 → Ω):=by apply aD.ext; rintro x; simp [m4]
    rw [he]
    simp [entropy,eo,m4]
  | succ n ih =>
    rw [TJ,Lg,wZ]
    simp only [ih,← Finset.sum_mul,p.dN,one_mul,Nat.cast_add,Nat.cast_one]
    ring
lemma SO (p:aD Ω) (n:ℕ) (i:Fin n) :
    p.f6 n = (p.joint (fun _ =>
      ({ mass:=fun x:(j:{j:Fin n // j ≠ i}) → Ω=>∏ j,p (x j)
         nonneg:=fun x=>Finset.prod_nonneg (fun j _=>p.nonneg _)
         dN:=by rw [← Fintype.prod_sum]; simp only [p.dN,Finset.prod_const_one] } :
            aD ((j:{j:Fin n // j ≠ i}) → Ω)))).map
      (Equiv.piSplitAt i (fun _:Fin n=>Ω)).symm:=by
  apply aD.ext; rintro x
  rw [lA]
  change (∏ j:Fin n,p (x j)) = p (x i)*(∏ j:{j:Fin n // j ≠ i},p (x j))
  rw [← Fintype.prod_subtype_mul_prod_subtype (p:=fun j:Fin n=>j=i)]
  have he:(∏ j:{j:Fin n // j=i},p (x j)) = p (x i):=by
    have hsub:=Finset.prod_subtype (F:=inferInstance) (p:=fun j:Fin n=>j=i) ({i}:Finset (Fin n)) (by simp) (fun j=>p (x j))
    simpa using hsub.symm
  convert! congrArg (fun v=>v*(∏ j:{j:Fin n // j ≠ i},p (x j))) he using 1
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_univ]
lemma Kk (p:aD Ω) (n:ℕ) (i:Fin n) :
    (p.f6 n).map (fun x=>x i) = p:=by
  rw [SO p n i,map_comp]
  have he:((fun x:Fin n → Ω=>x i) ∘ (Equiv.piSplitAt i (fun _:Fin n=>Ω)).symm) = Prod.fst:=by
    funext x
    simp [Equiv.piSplitAt]
  rw [he,qM]
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD dD g4 oG Mc RO c9
namespace GaussianMoat
section
open scoped BigOperators Classical
namespace aD
variable {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
lemma Km (p:aD Ω) (f:Ω → α) (q:α → aD β) :
    (p.map f).mix q = p.mix (fun ω=>q (f ω)):=by
  apply aD.ext; rintro b
  simp only [kV,f7,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp
lemma Xy (p:aD Ω) (q:Ω → aD α) (r:α → aD β) :
    (p.mix q).mix r = p.mix (fun ω=>(q ω).mix r):=by
  apply aD.ext; rintro b
  simp only [kV,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  ring
lemma yJ (p:aD Ω) (q:Ω → aD α) (F:Ω → α → β) :
    (p.joint q).map (fun v=>F v.1 v.2) = p.mix (fun ω=>(q ω).map (F ω)):=by
  have h:=congrArg (fun r:aD (Ω × β)=>r.map Prod.snd) (ow p q F)
  simpa only [map_comp,qN,Function.comp_def] using h
lemma Uz (p:aD Ω) (q:Ω → aD α) (r:Ω → α → aD β) :
    ((p.joint q).joint (fun v=>r v.1 v.2)).map (fun v=>(v.1.1,(v.1.2,v.2))) =
      p.joint (fun ω=>(q ω).joint (r ω)):=by
  apply aD.ext; rintro v
  rcases v with ⟨ω,a,b⟩
  change ((p.joint q).joint (fun v=>r v.1 v.2)).map (Equiv.prodAssoc Ω α β) (ω,a,b) = _
  rw [lA]
  simp only [Equiv.prodAssoc_symm_apply,jv,mul_assoc]
end aD
structure aO where
  bound:ℕ
  law:ℕ → aD (Fin (bound+1))
noncomputable def ko (n m:ℕ):Fin (n+1) × Fin (m+1) → Fin (n+m+1) :=
  fun v=>⟨v.1.val+v.2.val,by omega⟩
noncomputable def aO.then (K R:aO):aO where
  bound:=K.bound+R.bound
  law:=fun a=>((K.law a).joint (fun i=>R.law (a+i.val))).map
    (ko K.bound R.bound)
noncomputable def nS (z:ℕ → GaussianInt) (n:ℕ):aO where
  bound:=n
  law:=fun a=>((aD.uniform Bool).joint (fun _ =>
    jh (fun t=>z (a+t)) n)).map (fun v=>if v.1 then v.2.1 else v.2.2)
noncomputable def dQ (n:ℕ):aO where
  bound:=n
  law:=fun _=>aD.uniform (Fin (n+1))
noncomputable def b9 (z:ℕ → GaussianInt) (ns:List ℕ) (N:ℕ):aO :=
  ns.foldr (fun n K=>(nS z n).then K) (dQ N)
@[simp] lemma jG (z:ℕ → GaussianInt) (ns:List ℕ) (N:ℕ) :
    (b9 z ns N).bound = ns.sum+N:=by
  induction ns with
  | nil=>simp [b9,dQ]
  | cons n ns ih =>
    change n+(b9 z ns N).bound = _
    rw [ih,List.sum_cons,Nat.add_assoc]
@[simp] lemma n6 (z:ℕ → GaussianInt) (n:ℕ) (ns:List ℕ) (N:ℕ) :
    b9 z (n::ns) N = (nS z n).then (b9 z ns N):=rfl
noncomputable def bR.advance (P:bR) (K:aO):bR where
  last:=P.last+K.bound
  law:=(P.law.joint (fun a=>K.law a.val)).map (ko P.last K.bound)
lemma aO.RQ (K:aO) (a:ℕ)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:1 ≤ D)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK:1 ≤ K.bound) :
    (K.law a).Hf (fun i=>z (a+i.val)-z a) ≤
      Real.log 36+2*Real.log (D*K.bound):=by
  apply je
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro i
    simpa only [Nat.add_zero] using g8 z (by linarith only [hD]) hstep
      a K.bound i.val 0 (by omega) (by omega)
lemma bR.vk (P:bR) (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:1 ≤ D)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK:1 ≤ K.bound) :
    (P.law.joint (fun a=>K.law a.val)).Hf
      (fun v=>z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*K.bound):=by
  apply je
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro v
    simpa only [Nat.add_zero] using g8 z (by linarith only [hD]) hstep
      v.1.val K.bound v.2.val 0 (by omega) (by omega)
lemma Gq {b q:ℕ} {L F E E' g e C:ℝ}
    (hq:0 < q) (hL:0 ≤ L) (hg:0 ≤ g) (hg1:g ≤ 1/100)
    (hbq:(b:ℝ) ≤ g*q) (hF:(1-30*g)*L ≤ F)
    (hE:(1-e)*(q:ℝ)*L ≤ E) (hC:C ≤ 8*g*q*L)
    (hstep:(b:ℝ)*((q-b:ℕ)*F+E-C) ≤ 2*(q:ℝ)*E') :
    (1-e/2-20*g)*(b:ℝ)*L ≤ E':=by
  have hqr:(0:ℝ) < q:=by exact_mod_cast hq
  have V7:(b:ℝ) ≤ q:=by nlinarith only [hbq,hg1,hqr]
  have V8:b ≤ q:=by exact_mod_cast V7
  rw [Nat.cast_sub V8] at hstep
  have XT:0 ≤ (q:ℝ)-b:=by linarith only [V7]
  have YO:=mul_le_mul_of_nonneg_left hF XT
  have hgl:0 ≤ (1-30*g)*L:=mul_nonneg (by linarith only [hg1]) hL
  have hbL:=mul_le_mul_of_nonneg_right hbq hgl
  have hgg:=mul_nonneg (mul_nonneg hg hg) (mul_nonneg hqr.le hL)
  have XZ:0 ≤ g*(q:ℝ)*L:=by positivity
  have WV:(2-e-40*g)*(q:ℝ)*L ≤ ((q:ℝ)-b)*F+E-C:=by
    nlinarith only [YO,hbL,hE,hC,hgg,XZ]
  have hm:=mul_le_mul_of_nonneg_left WV (Nat.cast_nonneg b:(0:ℝ) ≤ b)
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num:(0:ℝ)<2) hqr)).mp
  calc
    _ = (b:ℝ)*((2-e-40*g)*(q:ℝ)*L):=by ring
    _ ≤ (b:ℝ)*(((q:ℝ)-b)*F+E-C):=hm
    _ ≤ _:=hstep
theorem bR.Qr (P:bR) (s:aE)
    (z:ℕ → GaussianInt) {D g e:ℝ} (hD:1 ≤ D)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q:ℕ}
    (hn:1 ≤ n) (hb:0 < b) (hbq:b < q) (hq:q ≤ s.primes.card)
    (hg:0 ≤ g) (hg1:g ≤ 1/100) (hL:0 ≤ s.aP)
    (hratio:(b:ℝ) ≤ g*q)
    (V9:∀ a:Fin (P.last+1),(1-30*g)*s.aP ≤ s.dV
      (jh (fun t=>z (a.val+t)) n)
      (fun ij=>z (a.val+ij.1.val)) (fun ij=>z (a.val+ij.2.val)) b (by omega))
    (hE:(1-e)*(q:ℝ)*s.aP ≤ s.aV P.law (fun a=>z a.val) q)
    (jz:2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.aP) :
    (1-e/2-20*g)*(b:ℝ)*s.aP ≤
      s.aV (P.step z n).law (fun a=>z a.val) b:=by
  exact Gq (by omega) hL hg hg1 hratio le_rfl hE jz
    (P.NU s z hD hstep hn hb hbq hq V9)
lemma Tv (l:ℕ) {g:ℝ} (hg:0 ≤ g) (e:ℕ → ℝ)
    (h0:e 0 ≤ 1) (hnext:∀ j < l,e (j+1) ≤ e j/2+20*g) :
    e l ≤ (1/2:ℝ)^l+40*g:=by
  induction l with
  | zero=>simpa only [pow_zero] using h0.trans (le_add_of_nonneg_right (by positivity))
  | succ l ih =>
    have hi:=ih (fun j hj=>hnext j (by omega))
    have hn:=hnext l (by omega)
    rw [pow_succ]
    linarith only [hi,hn]
end
section
namespace aD
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
lemma gW (p:aD Ω) (q:Ω → aD α) (F:Ω × α → β) :
    (p.joint q).map F = p.mix (fun ω=>(q ω).map (fun a=>F (ω,a))):=by
  exact yJ p q (fun ω a=>F (ω,a))
lemma TK (p:aD Ω) (q:aD α) (r:Ω → α → aD β) :
    p.mix (fun ω=>q.mix (r ω)) = q.mix (fun a=>p.mix (fun ω=>r ω a)):=by
  apply aD.ext; rintro b
  simp only [kV,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  ring
end aD
open scoped BigOperators Classical
lemma bR.Kp (P:bR) (z:ℕ → GaussianInt) (n:ℕ) :
    P.advance (nS z n) = P.step z n:=by
  unfold bR.advance bR.step nS
  congr 1
  dsimp only
  rw [aD.gW]
  conv_lhs=>arg 2; ext a; rw [aD.map_comp,aD.gW]
  rw [aD.TK,aD.gW]
  conv_rhs=>arg 2; ext c; rw [aD.gW]
  apply congrArg
  funext c
  apply congrArg
  funext a
  apply congrArg
  funext ij
  apply Fin.ext
  dsimp only [Function.comp_def,ko,r9]
  split_ifs <;> rfl
end
namespace aD
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} {δ:Type oG} {ε:Type Mc} [Fintype Ω]
noncomputable def i7 (p:aD Ω) (X:Ω → α) (Y:Ω → β) (O:Ω → γ):ℝ :=
  p.bT X O-p.bT X (fun ω=>(O ω,Y ω))
lemma WX (p:aD Ω) (X:Ω → α) (Y:Ω → β) (O:Ω → γ) :
    0 ≤ p.i7 X Y O:=sub_nonneg.mpr (p.u7 X O Y)
lemma oO (p:aD Ω) (X:Ω → α) (Y:Ω → β) (O:Ω → γ) :
    p.i7 X Y O = p.i7 Y X O:=by
  unfold i7 bT
  have he:p.Hf (fun ω=>(X ω,(O ω,Y ω))) =
      p.Hf (fun ω=>(Y ω,(O ω,X ω))):=by
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  rw [he,p.kd O Y,p.kd O X]
  ring
lemma RU (p:aD Ω) (X:Ω → α) (Y:Ω → β) (O:Ω → γ) :
    p.i7 X Y O ≤ p.bT X O:=by
  have h:=p.F7 X (fun ω=>(O ω,Y ω))
  unfold i7
  linarith
lemma SX (p:aD Ω) (X:Ω → α) (Y:Ω → β) (O:Ω → γ) :
    p.i7 X Y O ≤ p.Hf Y:=by
  rw [p.oO]
  exact (p.RU Y X O).trans (p.C8 Y O)
lemma SY (p:aD Ω) (X:Ω → α) (Y:Ω → β) (Z:Ω → δ) (O:Ω → γ) :
    p.i7 X (fun ω=>(Y ω,Z ω)) O =
      p.i7 X Y O+p.i7 X Z (fun ω=>(O ω,Y ω)):=by
  unfold i7
  have he:p.bT X (fun ω=>(O ω,(Y ω,Z ω))) =
      p.bT X (fun ω=>((O ω,Y ω),Z ω)):=by
    unfold bT
    rw [p.Pk O Y Z]
    congr 1
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq,and_assoc]
  rw [he]
  ring
lemma EO (p:aD Ω) (X:Ω → α) (Y:Ω → β)
    (O:Ω → γ) (S:Ω → δ) :
    p.i7 X Y (fun ω=>(O ω,S ω)) ≤ p.i7 X Y O+p.Hf S:=by
  have h1:=p.u7 X O S
  have h2:=p.u7 S O Y
  have h3:=p.C8 S O
  have h4:=p.F7 S (fun ω=>(X ω,(O ω,Y ω)))
  have h5:=p.vT X S (fun ω=>(O ω,Y ω))
  have h6:=p.vT S X (fun ω=>(O ω,Y ω))
  have he:p.bT (fun ω=>(X ω,S ω)) (fun ω=>(O ω,Y ω)) =
      p.bT (fun ω=>(S ω,X ω)) (fun ω=>(O ω,Y ω)):=by
    unfold bT
    congr 1
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  have he':p.bT X (fun ω=>((O ω,S ω),Y ω)) =
      p.bT X (fun ω=>(S ω,(O ω,Y ω))):=by
    unfold bT
    congr 1 <;> apply p.aZ <;> intro ω ν <;>
      simp only [Prod.mk.injEq] <;> tauto
  unfold i7
  rw [he']
  linarith only [h1,h2,h3,h4,h5,h6,he]
theorem Pw (p:aD Ω) (X:Ω → α) (O:Ω → β)
    (X':Ω → γ) (O':Ω → δ) (W:Ω → ε) {ζ:Type RO} (S:Ω → ζ)
    (hO:∀ ω ν,(O ω,S ω)=(O ν,S ν) ↔ (O' ω,S ω)=(O' ν,S ν))
    (hX:∀ ω ν,(X ω,O ω,S ω)=(X ν,O ν,S ν) ↔
      (X' ω,O' ω,S ω)=(X' ν,O' ν,S ν)) :
    p.i7 X (fun ω=>(S ω,W ω)) O ≤ p.i7 X' W O'+2*p.Hf S:=by
  have he:p.i7 X W (fun ω=>(O ω,S ω)) =
      p.i7 X' W (fun ω=>(O' ω,S ω)):=by
    rw [p.oO X W,p.oO X' W]
    unfold i7 bT
    congr 2
    · apply p.aZ
      intro ω ν
      simp only [Prod.mk.injEq,hO]
    · exact p.aZ _ _ hO
    · apply p.aZ
      intro ω ν
      have hh:=hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
    · apply p.aZ
      intro ω ν
      have hh:=hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
  rw [p.SY X S W O,he]
  have h1:=p.SX X S O
  have h2:=p.EO X' W O' S
  linarith
lemma SZ [Fintype β] (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.bT X Y = ∑ a,p.map Y a*(p.eO Y a).Hf X:=by
  let C:=ju X
  have hh:=p.Gp C Y
  have hx (r:aD Ω):r.Hf C = r.Hf X:=by
    apply r.aZ
    intro ω ν
    exact gO X ω ν
  have hpair:p.Hf (fun ω=>(C ω,Y ω)) = p.Hf (fun ω=>(X ω,Y ω)):=by
    apply p.aZ
    intro ω ν
    simp only [Prod.mk.injEq,C,gO]
  simpa only [g7,← jW,hx,hpair,bT] using hh
end aD
open scoped BigOperators Classical
theorem aE.v9 {Ω:Type bU} [Fintype Ω]
    (s:aE) (p:aD Ω) (X Y:Ω → GaussianInt) (b:ℕ) :
    s.aV p X b ≤ s.aV p Y b+p.Hf (fun ω=>Y ω-X ω):=by
  have h (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) :
      p.Hf (aD.aF (fun ω=>s.bC σ (X ω)) π b) ≤
        p.Hf (aD.aF (fun ω=>s.bC σ (Y ω)) π b)+
          p.Hf (fun ω=>Y ω-X ω):=by
    apply (p.lN _ (fun ω =>
      (aD.aF (fun ν=>s.bC σ (Y ν)) π b ω,Y ω-X ω)) ?_).trans
      (p.kJ _ _)
    intro ω ν hh
    funext i
    by_cases hi:i.val<b
    · have hy:s.bC σ (Y ω) (π i)=s.bC σ (Y ν) (π i):=by
        simpa [aD.aF,hi] using congrFun (congrArg Prod.fst hh) i
      have hd:=congrArg (aR (dG (s.factor (s.enumeration (π i))) (σ (π i)))) (congrArg Prod.snd hh)
      have hx:=kR hy hd
      simpa only [sub_sub_cancel,aE.bC,aD.aF,hi,dO]
        using congrArg some hx
    · simp [aD.aF,hi]
  have hh:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s:=Finset.univ) (fun π _=>h σ π))
  simpa only [aE.aV,aD.gP,aD.bF,
    Finset.expect_add_distrib,Fintype.expect_const] using hh
lemma k4 {Ω:Type bU} {ι:Type c9} (f:ι → GaussianInt)
    (X Y:Ω → GaussianInt) (ω ν:Ω) :
    ((fun i=>aR (f i) (X ω)),Y ω-X ω)=
      ((fun i=>aR (f i) (X ν)),Y ν-X ν) ↔
    ((fun i=>aR (f i) (Y ω)),Y ω-X ω)=
      ((fun i=>aR (f i) (Y ν)),Y ν-X ν):=by
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hx,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h:=Da (congrFun hx i) (congrArg (aR (f i)) hd)
    simpa only [add_sub_cancel] using h
  · rintro ⟨hy,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h:=kR (congrFun hy i) (congrArg (aR (f i)) hd)
    simpa only [sub_sub_cancel] using h
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD
namespace GaussianMoat
open scoped BigOperators Classical
structure jK (s:aE) (D g:ℝ) (n b q:ℕ):Prop where
  length_pos:1 ≤ n
  RV:0 < b
  decreases:b < q
  S5:q ≤ s.primes.card
  ratio:(b:ℝ) ≤ g*q
  log_pos:0 < Real.log n-Real.log 18
  rounding:s.aP ≤ g*(Real.log n-Real.log 18)
  large:5120*s.aP ≤ g^4*(Real.log n-Real.log 18)
  Rb:(b:ℝ)*s.aP ≤ g*(Real.log n-Real.log 18)
  Qt:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ)) ≤
    g*(Real.log n-Real.log 18)
  Qv:2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*s.aP
  Lh:2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.aP
theorem bR.DG (P:bR) (s:aE)
    (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) (hinj:Function.Injective z)
    {D T g e:ℝ} (hD:1 ≤ D) (hT:5 ≤ T)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg:0 < g) (hg1:g ≤ 1/100) (hL:1 ≤ s.aP) {n b q:ℕ}
    (hm:jK s D g n b q)
    (hE:(1-e)*(q:ℝ)*s.aP ≤ s.aV P.law (fun a=>z a.val) q) :
    (1-e/2-20*g)*(b:ℝ)*s.aP ≤
      s.aV (P.step z n).law (fun a=>z a.val) b:=by
  apply P.Qr s z hD hstep hm.length_pos hm.RV hm.decreases
    hm.S5 hg.le hg1 (by linarith only [hL]) hm.ratio ?_ hE hm.Lh
  intro a
  obtain ⟨hb,hh⟩:=s.Mt hne (fun t=>z (a.val+t)) hm.length_pos
    (DB z hinj a.val) hD hT
    (fun t _=>by simpa only [Nat.add_assoc] using hstep (a.val+t)) hpT hg hg1 hL
    hm.log_pos hm.rounding hm.large hm.Rb hm.Qt hm.Qv
  exact hh
lemma aE.Jj {Ω:Type bU} [Fintype Ω]
    (s:aE) (p:aD Ω) (Z:Ω → GaussianInt) (b:ℕ) :
    0 ≤ s.aV p Z b:=by
  unfold aV aD.gP
  exact Finset.expect_nonneg (fun _ _=>p.Ew _ _)
noncomputable def bR.run (P:bR) (z:ℕ → GaussianInt) (n:ℕ → ℕ):ℕ → bR
  | 0=>P
  | j+1=>(P.run z n j).step z (n j)
@[simp] lemma bR.TQ (P:bR) (z:ℕ → GaussianInt) (n:ℕ → ℕ) :
    P.run z n 0=P:=rfl
@[simp] lemma bR.Qw (P:bR) (z:ℕ → GaussianInt) (n:ℕ → ℕ) (j:ℕ) :
    P.run z n (j+1)=(P.run z n j).step z (n j):=rfl
theorem bR.LG (P:bR) (s:aE) (hne:s.primes.Nonempty)
    (z:ℕ → GaussianInt) (hinj:Function.Injective z) {D T g:ℝ}
    (hD:1 ≤ D) (hT:5 ≤ T) (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg:0 < g) (hg1:g ≤ 1/100) (hL:1 ≤ s.aP)
    (n q:ℕ → ℕ) (l:ℕ) (hm:∀ j<l,jK s D g (n j) (q (j+1)) (q j)) :
    (1-(1/2:ℝ)^l-40*g)*(q l:ℝ)*s.aP ≤
      s.aV (P.run z n l).law (fun a=>z a.val) (q l):=by
  induction l with
  | zero =>
    have hh:=s.Jj P.law (fun a=>z a.val) (q 0)
    simp only [pow_zero,sub_self,zero_sub,bR.TQ]
    have hneg : -(40*g)*(q 0:ℝ)*s.aP ≤ 0:=by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hg]) (Nat.cast_nonneg (q 0))
      · linarith only [hL]
    exact hneg.trans hh
  | succ l ih =>
    have hi:=ih (fun j hj=>hm j (by omega))
    have hh:=(P.run z n l).DG s hne z hinj hD hT hstep hpT
      hg hg1 hL (hm l (by omega)) (e:=(1/2:ℝ)^l+40*g) (by
        convert hi using 1; ring)
    rw [bR.Qw]
    convert hh using 1; ring
theorem bR.NV (P:bR) (K:aO) (s:aE)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:1 ≤ D)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK:1 ≤ K.bound) (b:ℕ) :
    s.aV P.law (fun a=>z a.val) b -
      (Real.log 36+2*Real.log (D*K.bound)) ≤
    s.aV (P.advance K).law (fun a=>z a.val) b:=by
  let Q:=P.law.joint (fun a=>K.law a.val)
  have hh:=s.v9 Q (fun v=>z v.1.val)
    (fun v=>z (v.1.val+v.2.val)) b
  have hfst:=s.jQ P.law (fun a=>K.law a.val) (fun a=>z a.val) b
  change s.aV Q (fun v=>z v.1.val) b = _ at hfst
  rw [hfst] at hh
  have he:s.aV (P.advance K).law (fun a=>z a.val) b =
      s.aV Q (fun v=>z (v.1.val+v.2.val)) b:=by
    unfold bR.advance
    rw [s.lG]
    rfl
  rw [he]
  have hc:=P.vk K z hD hstep hK
  linarith only [hh,hc]
theorem bR.S6 (P:bR) (K:aO) (s:aE)
    (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) (hinj:Function.Injective z)
    {D T g:ℝ} (hD:1 ≤ D) (hT:5 ≤ T)
    (hstep:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT:∀ p ∈ s.primes,T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg:0 < g) (hg1:g ≤ 1/100) (hL:1 ≤ s.aP)
    (n q:ℕ → ℕ) (l:ℕ) (hm:∀ j<l,jK s D g (n j) (q (j+1)) (q j))
    (hK:1 ≤ K.bound) {e:ℝ}
    (jz:Real.log 36+2*Real.log (D*K.bound) ≤ e*(q l:ℝ)*s.aP) :
    (1-(1/2:ℝ)^l-40*g-e)*(q l:ℝ)*s.aP ≤
      s.aV ((P.run z n l).advance K).law (fun a=>z a.val) (q l):=by
  have h1:=P.LG s hne z hinj hD hT hstep hpT hg hg1 hL n q l hm
  have h2:=(P.run z n l).NV K s z hD hstep hK (q l)
  nlinarith only [h1,h2,jz]
noncomputable def bR.observe {α:Type cD} [Fintype α] (P:bR) (f:ℕ → α):aD α :=
  P.law.map (fun t=>f t.val)
lemma bR.qG (P Q:bR) (hl:P.last=Q.last)
    (h:∀ {α:Type} [Fintype α] (f:ℕ → α),P.observe f=Q.observe f):P=Q:=by
  cases P with | mk n p =>
  cases Q with | mk m q =>
  dsimp only at hl
  subst m
  congr 1
  let f:ℕ → Fin (n+1):=fun t=>⟨min t n,by omega⟩
  have hh:=h f
  have he:(fun t:Fin (n+1)=>f t.val)=id:=by
    funext t
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  unfold observe at hh
  simpa only [he,aD.map_id] using hh
lemma bR.Dd {α:Type cD} [Fintype α]
    (P:bR) (K:aO) (f:ℕ → α) :
    (P.advance K).observe f=P.law.mix (fun a=>(K.law a.val).map (fun t=>f (a.val+t.val))):=by
  unfold observe advance
  rw [aD.map_comp,aD.gW]
  rfl
lemma aO.m6 {α:Type cD} [Fintype α]
    (K R:aO) (a:ℕ) (f:ℕ → α) :
    ((K.then R).law a).map (fun t=>f (a+t.val))=
      (K.law a).mix (fun t=>(R.law (a+t.val)).map (fun u=>f (a+t.val+u.val))):=by
  unfold aO.then
  rw [aD.map_comp,aD.gW]
  congr 1
  funext t
  congr 1
  funext u
  simp only [Function.comp_def,ko,Nat.add_assoc]
lemma bR.Bd (P:bR) (K R:aO) :
    P.advance (K.then R)=(P.advance K).advance R:=by
  apply bR.qG
  · exact (Nat.add_assoc _ _ _).symm
  · intro α _ f
    rw [bR.Dd,bR.Dd]
    change P.law.mix _ = (((P.law.joint (fun a=>K.law a.val)).map
      (ko P.last K.bound))).mix (fun a:Fin (P.last+K.bound+1) =>
        (R.law a.val).map (fun t=>f (a.val+t.val)))
    rw [aD.Km]
    have hj:=aD.yJ (P.law) (fun a=>K.law a.val)
      (fun a t=>(a,t))
    clear hj
    have Ya:((P.law.joint (fun a=>K.law a.val))).mix
        (fun v=>(R.law (v.1.val+v.2.val)).map (fun u=>f (v.1.val+v.2.val+u.val))) =
      P.law.mix (fun a=>(K.law a.val).mix
        (fun t=>(R.law (a.val+t.val)).map (fun u=>f (a.val+t.val+u.val)))):=by
      apply aD.ext; rintro x
      simp only [aD.kV,aD.jv,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    change P.law.mix _ = (P.law.joint (fun a=>K.law a.val)).mix
      (fun v=>(R.law (v.1.val+v.2.val)).map (fun u=>f (v.1.val+v.2.val+u.val)))
    rw [Ya]
    congr 1
    funext a
    exact K.m6 R a.val f
lemma bR.Jk (P:bR) (z:ℕ → GaussianInt)
    (n:ℕ) (ns:List ℕ) (N:ℕ) :
    P.advance (b9 z (n::ns) N)=(P.step z n).advance (b9 z ns N):=by
  rw [n6,bR.Bd,bR.Kp]
lemma bR.m7 (P:bR) (z:ℕ → GaussianInt)
    (ns ms:List ℕ) (N:ℕ) :
    P.advance (b9 z (ns++ms) N)=
      (ns.foldl (fun Q k=>Q.step z k) P).advance (b9 z ms N):=by
  induction ns generalizing P with
  | nil=>rfl
  | cons k ks hk =>
    rw [List.cons_append,bR.Jk,hk,List.foldl_cons]
lemma bR.NW (P:bR) (z:ℕ → GaussianInt)
    (n:ℕ → ℕ) (l:ℕ) :
    (List.ofFn (fun i:Fin l=>n i.val)).foldl (fun Q k=>Q.step z k) P=P.run z n l:=by
  induction l with
  | zero=>rfl
  | succ l hl =>
    rw [List.ofFn_succ_last,List.foldl_append,List.foldl_cons,List.foldl_nil]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [hl,bR.Qw]
lemma bR.WZ (P:bR) (z:ℕ → GaussianInt)
    (n:ℕ → ℕ) (l N:ℕ) :
    P.advance (b9 z (List.ofFn (fun i:Fin l=>n i.val)) N)=
      (P.run z n l).advance (dQ N):=by
  have h:=P.m7 z (List.ofFn (fun i:Fin l=>n i.val)) [] N
  simpa only [List.append_nil,bR.NW,b9,List.foldr_nil] using h
lemma Py {x:ℝ} (hx:2 ≤ x) :
    1 ≤ ⌊Real.exp x⌋₊ ∧ x-1 ≤ Real.log (⌊Real.exp x⌋₊:ℝ) ∧
      Real.log (⌊Real.exp x⌋₊:ℝ) ≤ x:=by
  have he:2 ≤ Real.exp x:=by linarith only [Real.add_one_le_exp x,hx]
  have hn:1 ≤ ⌊Real.exp x⌋₊:=Nat.floor_pos.mpr (by linarith only [he])
  have hnp:(0:ℝ)<⌊Real.exp x⌋₊:=by exact_mod_cast hn
  have kT:Real.exp x/2 ≤ (⌊Real.exp x⌋₊:ℝ):=by
    have h:=Nat.lt_floor_add_one (Real.exp x)
    linarith only [he,h]
  have hlo:=Real.log_le_log (div_pos (Real.exp_pos x) (by norm_num:(0:ℝ)<2)) kT
  rw [Real.log_div (Real.exp_ne_zero x) (by norm_num:(2:ℝ)≠0),Real.log_exp] at hlo
  have hl2:Real.log 2 ≤ 1:=by
    have h:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    linarith only [h]
  have hhi:=Real.log_le_log hnp (Nat.floor_le (Real.exp_nonneg x))
  rw [Real.log_exp] at hhi
  exact ⟨hn,by linarith only [hlo,hl2],hhi⟩
theorem jK.RW (s:aE) {D U g:ℝ}
    (hD:1 ≤ D) (hg:0 < g) (hg1:g ≤ 1/200) (hL:1 ≤ s.aP)
    (hU:0 < U)
    (hlog:2*(1+Real.log 18) ≤ g*U)
    (cQ:640*s.aP ≤ g^5*U)
    (hsize:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ)) ≤ g^2*U)
    (sw:4*Real.log D+2*Real.log 36 ≤ 4*g*U)
    (sI:2*Real.log 16+4*Real.log D ≤ U/4)
    (hcap:⌊U/s.aP⌋₊ ≤ s.primes.card) :
    jK s D (2*g) ⌊Real.exp (g*U)⌋₊
      ⌊g^2*U/s.aP⌋₊ ⌊U/s.aP⌋₊:=by
  let L:=s.aP
  let n:=⌊Real.exp (g*U)⌋₊
  let q:=⌊U/L⌋₊
  let b:=⌊g^2*U/L⌋₊
  have hLp:0 < L:=by dsimp [L]; linarith only [hL]
  have hg_le:g ≤ 1:=by linarith only [hg1]
  have hg2:g^2 ≤ 1:=pow_le_one₀ hg.le hg_le
  have hg3:g^3 ≤ 1:=pow_le_one₀ hg.le hg_le
  have h52:g^5*U ≤ g^2*U:=by
    have hpow:g^5=g^2*g^3:=by ring
    rw [hpow]
    nlinarith only [hg3,mul_nonneg (sq_nonneg g) hU.le]
  have h2U:g^2*U ≤ U:=by nlinarith only [hg2,hU]
  have hLU:L ≤ U/2:=by
    change 640*L ≤ g^5*U at cQ
    linarith only [cQ,h52,h2U,hLp]
  have hbL:L ≤ g^2*U:=by
    change 640*L ≤ g^5*U at cQ
    linarith only [cQ,h52,hLp]
  have he2:2 ≤ g*U:=by
    have hh:=Real.log_nonneg (by norm_num:(1:ℝ)≤18)
    linarith only [hh,hlog]
  obtain ⟨hn,RY,Mz⟩:=Py he2
  have NY:g*U/2 ≤ Real.log n-Real.log 18:=by
    change g*U-1 ≤ Real.log n at RY
    linarith only [RY,hlog]
  have hu:0 < Real.log n-Real.log 18 :=
    lt_of_lt_of_le (div_pos (mul_pos hg hU) (by norm_num)) NY
  have YP:U-L ≤ (q:ℝ)*L:=by
    have hf:=Nat.lt_floor_add_one (U/L)
    have hm:=mul_lt_mul_of_pos_right hf hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    linarith only [hm]
  have hqU:U/2 ≤ (q:ℝ)*L:=by linarith only [YP,hLU]
  have hqpos:0 < q:=by
    have:(0:ℝ)<q:=by nlinarith only [hqU,hU,hLp]
    exact_mod_cast this
  have hbpos:0 < b:=by
    apply Nat.floor_pos.mpr
    exact (le_div_iff₀ hLp).mpr (by simpa only [one_mul] using hbL)
  have Wa:(b:ℝ)*L ≤ g^2*U:=by
    exact (le_div_iff₀ hLp).mp (Nat.floor_le (by positivity:0 ≤ g^2*U/L))
  have hratio:(b:ℝ) ≤ (2*g)*q:=by
    have h1:=mul_le_mul_of_nonneg_left hqU (show 0 ≤ 2*g by positivity)
    have h2:g^2*U ≤ g*U:=by
      have hh:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg_le hg.le) hU.le
      simpa only [mul_one,pow_two] using hh
    apply (mul_le_mul_iff_left₀ hLp).mp
    nlinarith only [Wa,h1,h2]
  have hbq:b < q:=by
    have hqr:(0:ℝ)<q:=by exact_mod_cast hqpos
    have:(b:ℝ)<q:=by nlinarith only [hratio,hg1,hqr]
    exact_mod_cast this
  refine ⟨hn,hbpos,hbq,hcap,hratio,hu,?_,?_,?_,?_,?_,?_⟩
  · have hm:=mul_le_mul_of_nonneg_left NY (show 0 ≤ 2*g by positivity)
    dsimp only [L] at hbL
    nlinarith only [hbL,hm]
  · have hm:=mul_le_mul_of_nonneg_left NY (show 0 ≤ (2*g)^4 by positivity)
    nlinarith only [cQ,hm]
  · have hm:=mul_le_mul_of_nonneg_left NY (show 0 ≤ 2*g by positivity)
    change (b:ℝ)*L ≤ _
    nlinarith only [Wa,hm]
  · have hm:=mul_le_mul_of_nonneg_left NY (show 0 ≤ 2*g by positivity)
    linarith only [hsize,hm]
  · have W0:(q:ℝ)*L ≤ s.primes.card*L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcap) hLp.le
    have hgU:=mul_le_mul_of_nonneg_right hg1 hU.le
    change 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*L
    change Real.log n ≤ g*U at Mz
    nlinarith only [Mz,sI,hqU,W0,hgU,hU]
  · have hm:=mul_le_mul_of_nonneg_left hqU (show 0 ≤ 16*g by positivity)
    have V5:D≠0:=by linarith only [hD]
    have hnR:(n:ℝ)≠0:=by exact_mod_cast (show n≠0 by omega)
    rw [Real.log_mul V5 hnR]
    change Real.log n ≤ g*U at Mz
    change 2*(Real.log 36+2*(Real.log D+Real.log n)) ≤ 8*(2*g)*q*L
    nlinarith only [Mz,sw,hm]
noncomputable def aW (g U:ℝ) (j:ℕ):ℝ:=(g^2)^j*U
noncomputable def f9 (g U:ℝ) (j:ℕ):ℕ:=⌊Real.exp (g*aW g U j)⌋₊
noncomputable def eD (s:aE) (g U:ℝ) (j:ℕ):ℕ:=⌊aW g U j/s.aP⌋₊
lemma lU {g U:ℝ} (hg:0<g) (hU:0<U) (j:ℕ) :
    0<aW g U j:=mul_pos (pow_pos (sq_pos_of_pos hg) _) hU
lemma l7 {g U:ℝ} (hg:0≤g) (hg1:g≤1) (hU:0≤U) :
    Antitone (aW g U):=by
  intro i j hij
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sq_nonneg g) (pow_le_one₀ hg hg1) hij) hU
lemma EU (g U:ℝ) (j:ℕ) :
    aW g U (j+1)=g^2*aW g U j:=by
  unfold aW
  rw [pow_succ]
  ring
theorem DH (s:aE) {D U g:ℝ} {l:ℕ}
    (hD:1≤D) (hg:0<g) (hg1:g≤1/200) (hL:1 ≤ s.aP) (hU:0<U)
    (hlog:2*(1+Real.log 18) ≤ g*aW g U l)
    (cQ:640*s.aP ≤ g^5*aW g U l)
    (hsize:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ)) ≤ g^2*aW g U l)
    (sw:4*Real.log D+2*Real.log 36 ≤ 4*g*aW g U l)
    (sI:2*Real.log 16+4*Real.log D ≤ aW g U l/4)
    (hcap:⌊U/s.aP⌋₊ ≤ s.primes.card) :
    ∀ j<l,jK s D (2*g) (f9 g U j)
      (eD s g U (j+1)) (eD s g U j):=by
  intro j hj
  have hmono:=l7 hg.le (show g≤1 by linarith only [hg1]) hU.le
  have kT:=hmono hj.le
  have Gh:=hmono (Nat.zero_le j)
  simp only [aW,pow_zero,one_mul] at Gh
  unfold f9 eD
  rw [EU]
  apply jK.RW s hD hg hg1 hL (lU hg hU j)
  · exact hlog.trans (mul_le_mul_of_nonneg_left kT hg.le)
  · exact cQ.trans (mul_le_mul_of_nonneg_left kT (pow_nonneg hg.le _))
  · exact hsize.trans (mul_le_mul_of_nonneg_left kT (sq_nonneg g))
  · exact sw.trans (mul_le_mul_of_nonneg_left kT (by positivity))
  · exact sI.trans (div_le_div_of_nonneg_right kT (by norm_num))
  · exact (Nat.floor_mono (div_le_div_of_nonneg_right Gh (by linarith only [hL]))).trans hcap
theorem bR.DJ (P:bR) (s:aE)
    (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) (hinj:Function.Injective z)
    {D T U g:ℝ} {l:ℕ} (hD:1≤D) (hT:5≤T)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg:0<g) (hg1:g≤1/200) (hL:1 ≤ s.aP) (hU:0<U)
    (hlog:2*(1+Real.log 18) ≤ g*aW g U l)
    (cQ:640*s.aP ≤ g^5*aW g U l)
    (hsize:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ)) ≤ g^2*aW g U l)
    (sw:4*Real.log D+2*Real.log 36 ≤ 4*g*aW g U l)
    (sI:2*Real.log 16+4*Real.log D ≤ aW g U l/4)
    (hcap:⌊U/s.aP⌋₊ ≤ s.primes.card) :
    (1-(1/2:ℝ)^l-80*g)*(eD s g U l:ℝ)*s.aP ≤
      s.aV (P.run z (f9 g U) l).law (fun a=>z a.val) (eD s g U l):=by
  have hm:=DH s hD hg hg1 hL hU hlog cQ hsize sw sI hcap
  have hh:=P.LG s hne z hinj hD hT hs hpT (by positivity:0<2*g)
    (by linarith only [hg1]:2*g≤1/100) hL (f9 g U) (eD s g U) l hm
  convert hh using 1; ring
lemma Bh (z:ℕ → GaussianInt) (ns:List ℕ) (N:ℕ) {x:ℝ}
    (hns:∀ n∈ns,(n:ℝ)≤Real.exp x) (hN:(N:ℝ)≤Real.exp x)
    (hlen:(ns.length+2:ℝ)≤Real.exp x) :
    Real.log (1+(b9 z ns N).bound:ℝ) ≤ 2*x:=by
  have hsum:(ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp x:=by
    induction ns with
    | nil=>simp
    | cons n ns ih =>
      have hn:=hns n (by simp)
      have ht:=ih (fun k hk=>hns k (by simp [hk]))
        (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hlen; linarith only [hlen])
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hn,ht]
  have hx:(1:ℝ)≤Real.exp x:=by
    have hlen0:(0:ℝ)≤ns.length:=Nat.cast_nonneg _
    linarith only [hlen,hlen0]
  have hall:(1+(b9 z ns N).bound:ℝ)≤Real.exp (2*x):=by
    rw [jG,Nat.cast_add]
    have hm:=mul_le_mul_of_nonneg_right hlen (Real.exp_nonneg x)
    rw [show 2*x=x+x by ring,Real.exp_add]
    nlinarith only [hsum,hN,hm,hx]
  have hlog:=Real.log_le_log (by positivity:(0:ℝ)<1+(b9 z ns N).bound) hall
  simpa only [Real.log_exp] using hlog
lemma Sz {D g V L:ℝ} {q S:ℕ}
    (hD:1≤D) (hg:0≤g) (hS:1≤S)
    (hq:V/2≤(q:ℝ)*L) (hlog:Real.log (1+(S:ℝ))≤2*g*V)
    (hconst:Real.log 36+2*Real.log D≤g*V) :
    Real.log 36+2*Real.log (D*S)≤10*g*q*L:=by
  have hSp:(0:ℝ)<S:=by exact_mod_cast hS
  have YQ:=Real.log_le_log hSp (show (S:ℝ)≤1+S by linarith)
  rw [Real.log_mul (by linarith only [hD]:D≠0) hSp.ne']
  have hq':=mul_le_mul_of_nonneg_left hq (show 0≤10*g by positivity)
  nlinarith only [YQ,hlog,hconst,hq']
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD dD
namespace GaussianMoat
open scoped BigOperators Classical
namespace aD
noncomputable def pure {Ω:Type bU} [Fintype Ω] (ω:Ω):aD Ω where
  mass ν:=if ν=ω then 1 else 0
  nonneg _:=by split_ifs <;> norm_num
  dN:=by simp
lemma Qy {Ω:Type bU} {α:Type cD} [Fintype Ω] [Fintype α] (ω:Ω) (q:Ω → aD α) :
    (pure ω).mix q=q ω:=by
  apply aD.ext; rintro a
  simp [kV,pure]
lemma DK {Ω:Type bU} {α:Type cD} {β:Type dD} [Fintype Ω] [Fintype α] [Fintype β]
    (ω:Ω) (q:Ω → aD α) (F:Ω × α → β) :
    ((pure ω).joint q).map F=(q ω).map (fun a=>F (ω,a)):=by
  rw [gW,Qy]
end aD
noncomputable def bR.at (a:ℕ):bR where
  last:=a
  law:=aD.pure ⟨a,by omega⟩
lemma bR.RZ (a:ℕ) (K:aO) :
    ((bR.at a).advance K).law=
      (K.law a).map (fun t=>(⟨a+t.val,by omega⟩:Fin (a+K.bound+1))):=by
  change ((aD.pure (⟨a,by omega⟩:Fin (a+1))).joint
    (fun t=>K.law t.val)).map (ko a K.bound)=_
  rw [aD.DK]
  rfl
lemma aE.oP (s:aE) (K:aO)
    (z:ℕ → GaussianInt) (a b:ℕ) :
    s.aV ((bR.at a).advance K).law (fun t=>z t.val) b=
      s.aV (K.law a) (fun t=>z (a+t.val)) b:=by
  rw [bR.RZ]
  change s.aV ((K.law a).map
    (fun t=>(⟨a+t.val,by omega⟩:Fin (a+K.bound+1)))) (fun t=>z t.val) b = _
  rw [s.lG]
  rfl
theorem bR.Gt (P:bR) (K:aO) (s:aE)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:1≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (b:ℕ) :
    s.aV P.law (fun a=>z a.val) b-
      (Real.log 36+2*Real.log (D*(K.bound+1))) ≤
    s.aV (P.advance K).law (fun a=>z a.val) b:=by
  let Q:=P.law.joint (fun a=>K.law a.val)
  have hh:=s.v9 Q (fun v=>z v.1.val)
    (fun v=>z (v.1.val+v.2.val)) b
  have hf:=s.jQ P.law (fun a=>K.law a.val) (fun a=>z a.val) b
  change s.aV Q (fun v=>z v.1.val) b=_ at hf
  rw [hf] at hh
  have he:s.aV (P.advance K).law (fun a=>z a.val) b=
      s.aV Q (fun v=>z (v.1.val+v.2.val)) b:=by
    unfold bR.advance
    rw [s.lG]
    rfl
  have hc:Q.Hf (fun v=>z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*(K.bound+1)):=by
    apply je
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast Nat.le_add_left 1 K.bound)
    · intro v
      have hd:=g8 z (by linarith only [hD]) hs
        v.1.val (K.bound+1) v.2.val 0 (by omega) (by omega)
      simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using hd
  rw [he]
  linarith only [hh,hc]
theorem sK (s:aE) (hne:s.primes.Nonempty)
    (z:ℕ → GaussianInt) (hinj:Function.Injective z)
    (pre post:List ℕ) (a N:ℕ) {D T U g e:ℝ} {l:ℕ}
    (hD:1≤D) (hT:5≤T) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg:0<g) (hg1:g≤1/200) (hL:1≤ s.aP) (hU:0<U)
    (hlog:2*(1+Real.log 18)≤g*aW g U l)
    (cQ:640*s.aP≤g^5*aW g U l)
    (hsize:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ))≤g^2*aW g U l)
    (sw:4*Real.log D+2*Real.log 36≤4*g*aW g U l)
    (sI:2*Real.log 16+4*Real.log D≤aW g U l/4)
    (hcap:⌊U/s.aP⌋₊≤ s.primes.card)
    (jz:Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1)) ≤
      e*(eD s g U l:ℝ)*s.aP) :
    (1-(1/2:ℝ)^l-80*g-e)*(eD s g U l:ℝ)*s.aP ≤
      s.aV ((b9 z
        (pre++List.ofFn (fun i:Fin l=>f9 g U i.val)++post) N).law a)
          (fun t=>z (a+t.val)) (eD s g U l):=by
  rw [← s.oP]
  rw [List.append_assoc,bR.m7,bR.m7,
    bR.NW]
  let P:=pre.foldl (fun Q k=>Q.step z k) (bR.at a)
  have h1:=P.DJ s hne z hinj hD hT hs hpT hg hg1 hL hU
    hlog cQ hsize sw sI hcap
  have h2:=(P.run z (f9 g U) l).Gt
    (b9 z post N) s z hD hs (eD s g U l)
  rw [jG] at h2
  change _ ≤ s.aV ((P.run z (f9 g U) l).advance (b9 z post N)).law
    (fun a=>z a.val) (eD s g U l)
  simp only [Nat.cast_add] at jz h2
  nlinarith only [h1,h2,jz]
lemma aO.qG (K R:aO) (hb:K.bound=R.bound)
    (h:∀ (a:ℕ) {α:Type} [Fintype α] (f:ℕ → α),
      (K.law a).map (fun t=>f (a+t.val))=(R.law a).map (fun t=>f (a+t.val))):K=R:=by
  cases K with | mk n p =>
  cases R with | mk m q =>
  dsimp only at hb
  subst m
  congr 1
  funext a
  let f:ℕ → Fin (n+1):=fun t=>⟨min (t-a) n,by omega⟩
  have hh:=h a f
  have he:(fun t:Fin (n+1)=>f (a+t.val))=id:=by
    funext t
    apply Fin.ext
    dsimp only [f,id_eq]
    omega
  simpa only [he,aD.map_id] using hh
lemma aO.then_assoc (K R S:aO) :
    (K.then R).then S=K.then (R.then S):=by
  apply aO.qG
  · exact Nat.add_assoc _ _ _
  · intro a α _ f
    rw [aO.m6,aO.m6]
    have hl:((K.then R).law a).mix
        (fun t=>(S.law (a+t.val)).map (fun u=>f (a+t.val+u.val))) =
        (K.law a).mix (fun t=>(R.law (a+t.val)).mix
          (fun u=>(S.law (a+t.val+u.val)).map (fun v=>f (a+t.val+u.val+v.val)))):=by
      unfold aO.then
      rw [aD.Km]
      apply aD.ext; rintro x
      simp only [aD.kV,aD.jv,Fintype.sum_prod_type,Finset.mul_sum,
        ko,Nat.add_assoc,mul_assoc]
    rw [hl]
    congr 1
    funext t
    exact (R.m6 S (a+t.val) f).symm
lemma aD.map_pure {Ω:Type bU} {α:Type cD} [Fintype Ω] [Fintype α]
    (ω:Ω) (f:Ω → α):(aD.pure ω).map f=aD.pure (f ω):=by
  apply aD.ext; rintro a
  simp only [aD.f7,aD.pure]
  rw [Finset.sum_eq_single ω]
  · simp only [ite_true,eq_comm]
  · intro ν _ hν
    simp [hν]
  · simp
lemma aD.OE {Ω:Type bU} {α:Type cD} [Fintype Ω] [Fintype α]
    (p:aD Ω) (f:Ω → α):p.mix (fun ω=>aD.pure (f ω))=p.map f:=by
  apply aD.ext; rintro a
  simp only [aD.kV,aD.pure,aD.f7,mul_ite,mul_one,mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [eq_comm]
lemma oQ (a:ℕ) :
    (dQ 0).law a=aD.pure (0:Fin 1):=by
  change aD.uniform (Fin 1)=aD.pure (0:Fin 1)
  apply aD.ext; rintro x
  have hx:x=0:=Subsingleton.elim _ _
  simp [aD.uniform,aD.pure,hx]
lemma aO.Xz (K:aO):K.then (dQ 0)=K:=by
  apply aO.qG
  · exact Nat.add_zero _
  · intro a α _ f
    rw [aO.m6]
    change (K.law a).mix (fun t=>(aD.uniform (Fin 1)).map
      (fun u=>f (a+t.val+u.val)))=_
    have hu:aD.uniform (Fin 1)=aD.pure (0:Fin 1):=oQ 0
    simp only [hu,aD.map_pure,Fin.val_zero,Nat.add_zero]
    exact aD.OE _ _
lemma aO.S7 (K:aO):(dQ 0).then K=K:=by
  apply aO.qG
  · exact Nat.zero_add _
  · intro a α _ f
    rw [aO.m6]
    change (aD.uniform (Fin 1)).mix
      (fun t=>(K.law (a+t.val)).map (fun u=>f (a+t.val+u.val)))=_
    have hu:aD.uniform (Fin 1)=aD.pure (0:Fin 1):=oQ 0
    rw [hu,aD.Qy]
    rfl
lemma m8 (z:ℕ → GaussianInt) (ns ms:List ℕ) (N:ℕ) :
    b9 z (ns++ms) N=(b9 z ns 0).then (b9 z ms N):=by
  induction ns with
  | nil=>exact (aO.S7 _).symm
  | cons n ns ih =>
    rw [List.cons_append,n6,n6,ih,aO.then_assoc]
end GaussianMoat
end OAI
end
section
namespace OAI
universe jY bU cD c9 dD gQ
namespace GaussianMoat
section
open scoped BigOperators Classical
variable {G:Type jY} [Fintype G] [AddGroup G]
noncomputable def jo (K E:Finset G) (x:G):ℕ :=
  (E.filter (fun y=>x+y ∈ K)).card
lemma MA (K E:Finset G) :
    (∑ x:G,jo K E x) = K.card*E.card:=by
  simp only [jo,Finset.card_filter]
  rw [Finset.sum_comm]
  have hh (y:G):(∑ x:G,if x+y ∈ K then (1:ℕ) else 0) = K.card:=by
    calc
      _ = ∑ x:G,if x ∈ K then (1:ℕ) else 0 :=
        Equiv.sum_comp (Equiv.addRight y) (fun x=>if x ∈ K then (1:ℕ) else 0)
      _ = K.card:=by simp
  simp only [hh,Finset.sum_const,smul_eq_mul]
  ring
noncomputable def e5 (K E:Finset G) (δ:ℝ):Finset G :=
  Finset.univ.filter (fun x=>δ*K.card < jo K E x)
lemma DM (K E:Finset G) (hK:K.Nonempty) {δ:ℝ} (hδ:0 < δ) :
    ((e5 K E δ).card:ℝ) ≤ E.card/δ:=by
  have hKp:(0:ℝ) < K.card:=by exact_mod_cast Finset.card_pos.mpr hK
  have hs:((e5 K E δ).card:ℝ)*(δ*K.card) ≤
      ∑ x:G,(jo K E x:ℝ):=by
    have h1:∑ x ∈ e5 K E δ,δ*K.card ≤
        ∑ x ∈ e5 K E δ,(jo K E x:ℝ):=by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    have h2:=Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (e5 K E δ))
      (fun x _ _=>(Nat.cast_nonneg (jo K E x): (0:ℝ)≤_))
    simpa only [Finset.sum_const,nsmul_eq_mul] using h1.trans h2
  have he:(∑ x:G,(jo K E x:ℝ)) = (K.card:ℝ)*E.card:=by
    exact_mod_cast MA K E
  rw [he] at hs
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hs,hKp]
lemma Kq (q:aD G) (K E:Finset G) {τ δ:ℝ}
    (hτ:0 ≤ τ) (hτ1:τ ≤ 3/8) (hδ:0 < δ) (hδ1:δ ≤ 1/64)
    (hq:∀ y ∉ E,(τ+4*δ)/(Fintype.card G:ℝ) ≤ q y)
    {x:G} (hx:x ∉ e5 K E δ) :
    (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ q.prob (fun y=>x+y ∈ K):=by
  have hne:=q.nonempty
  have hp:(0:ℝ) < Fintype.card G:=by exact_mod_cast Fintype.card_pos
  have hoc:(jo K E x:ℝ) ≤ δ*K.card:=by
    simpa only [e5,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hx
  let S:=Finset.univ.filter (fun y:G=>x+y ∈ K ∧ y ∉ E)
  have hcount:(S.card:ℝ)+(jo K E x:ℝ) = K.card:=by
    have ht:S.card+jo K E x=K.card:=by
      have hbase:(Finset.univ.filter (fun y:G=>x+y ∈ K)).card = K.card:=by
        simp only [Finset.card_filter]
        calc
          _ = ∑ y:G,if y ∈ K then (1:ℕ) else 0 :=
            Equiv.sum_comp (Equiv.addLeft x) (fun y=>if y ∈ K then (1:ℕ) else 0)
          _ = K.card:=by simp
      have hsplit:=Finset.card_filter_add_card_filter_not
        (s:=Finset.univ.filter (fun y:G=>x+y ∈ K)) (p:=fun y=>y ∈ E)
      have hE:((Finset.univ.filter (fun y:G=>x+y ∈ K)).filter (fun y=>y ∈ E)).card =
          jo K E x:=by
        unfold jo
        congr 1
        ext y
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        tauto
      have hS:(Finset.univ.filter (fun y:G=>x+y ∈ K)).filter (fun y=>y ∉ E) = S:=by
        ext y
        simp [S]
      rw [hE,hS,hbase] at hsplit
      omega
    exact_mod_cast ht
  have h1:(S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) ≤ ∑ y ∈ S,q y:=by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s:=S)
      (fun y hy=>hq y (Finset.mem_filter.mp hy).2.2)
  have h2:(∑ y ∈ S,q y) ≤ q.prob (fun y=>x+y ∈ K):=by
    have he:q.prob (fun y=>x+y ∈ K) =
        ∑ y ∈ Finset.univ.filter (fun y:G=>x+y ∈ K),q y:=by
      simp only [aD.prob,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy:x+y ∈ K <;> simp only [hy,ite_true,ite_false]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,(Finset.mem_filter.mp hy).2.1⟩
    · intro y _ _
      exact q.nonneg y
  have h3:(τ+2*δ)*K.card ≤ S.card*(τ+4*δ):=by
    have hc:(0:ℝ) ≤ K.card:=Nat.cast_nonneg _
    have hd:τ+2*δ ≤ (1-δ)*(τ+4*δ):=by nlinarith only [hτ1,hδ1,hδ]
    have hm:=mul_le_mul_of_nonneg_right hd hc
    have hs:(1-δ)*(K.card:ℝ) ≤ S.card:=by linarith only [hcount,hoc]
    have ht:=mul_le_mul_of_nonneg_right hs (by positivity:(0:ℝ) ≤ τ+4*δ)
    nlinarith only [hm,ht]
  calc
    _ ≤ (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)):=by
      simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hp).mpr h3
    _ ≤ _:=h1.trans h2
noncomputable def iE (K:Finset G) (n:ℕ) (τ δ:ℝ) (h:Fin n → G):Finset G :=
  Finset.univ.filter (fun x =>
    (∑ i:Fin n,if x+h i ∈ K then (1:ℝ) else 0) ≤
      n*(τ+δ)*K.card/(Fintype.card G:ℝ))
theorem Lj (q:aD G) (K E:Finset G) (hK:K.Nonempty)
    {τ δ:ℝ} (hτ:0 ≤ τ) (hτ1:τ ≤ 3/8) (hδ:0 < δ) (hδ1:δ ≤ 1/64)
    (hq:∀ y ∉ E,(τ+4*δ)/(Fintype.card G:ℝ) ≤ q y) (n:ℕ) :
    (q.f6 n).prob (fun h=>¬ iE K n τ δ h ⊆ e5 K E δ) ≤
      (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))):=by
  have hne:=q.nonempty
  have hp:(0:ℝ) < Fintype.card G:=by exact_mod_cast Fintype.card_pos
  have hKp:(0:ℝ) < K.card:=by exact_mod_cast Finset.card_pos.mpr hK
  let μ:=(τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ)
  let d:=δ*(K.card:ℝ)/(Fintype.card G:ℝ)
  have hμ:0 < μ:=by dsimp [μ]; positivity
  have hd:0 ≤ d:=by dsimp [d]; positivity
  have hx (x:G):(q.f6 n).prob (fun h=>x ∈ iE K n τ δ h ∧
      x ∉ e5 K E δ) ≤
      Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))):=by
    by_cases he:x ∈ e5 K E δ
    · simp only [he,not_true_eq_false,and_false,aD.prob,ite_false,Finset.sum_const_zero]
      exact (Real.exp_pos _).le
    · have hh:=q.OD (fun y=>x+y ∈ K) n hμ hd
        (Kq q K E hτ hτ1 hδ hδ1 hq he)
      have YS:(n:ℝ)*(μ-d) = (n:ℝ)*(τ+δ)*K.card/(Fintype.card G:ℝ):=by
        dsimp [μ,d]
        ring
      rw [YS] at hh
      have hm:(q.f6 n).prob (fun h=>x ∈ iE K n τ δ h ∧
          x ∉ e5 K E δ) ≤
          (q.f6 n).prob (fun h =>
            (∑ i:Fin n,if x+h i ∈ K then (1:ℝ) else 0) ≤
              n*(τ+δ)*K.card/(Fintype.card G:ℝ)):=by
        apply aD.v7
        intro h hh
        exact (Finset.mem_filter.mp hh.1).2
      apply (hm.trans (by
        convert! hh using 1
        congr 1
        funext v
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi:x+v i ∈ K <;> simp only [hi,ite_true,ite_false])).trans
      apply Real.exp_le_exp.mpr
      have heq:d^2/μ = δ^2*(K.card:ℝ)/((τ+2*δ)*(Fintype.card G:ℝ)):=by
        dsimp [d,μ]
        field_simp
      have ht:0 < τ+2*δ:=by positivity
      have ht1:τ+2*δ ≤ 1:=by linarith only [hτ1,hδ1]
      have hratio:δ^2*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ d^2/μ:=by
        rw [heq]
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos ht hp)
        exact mul_le_of_le_one_left hp.le ht1
      have hmul:=mul_le_mul_of_nonneg_left hratio (show (0:ℝ) ≤ n/2 by positivity)
      calc
        _ = -((n:ℝ)/2*(d^2/μ)):=by simp only [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ -((n:ℝ)/2*(δ^2*(K.card:ℝ)/(Fintype.card G:ℝ))):=neg_le_neg hmul
        _ = _:=by ring
  have hu:=(q.f6 n).Kj (fun x h=>x ∈ iE K n τ δ h ∧
    x ∉ e5 K E δ)
  have hm:(q.f6 n).prob (fun h=>¬ iE K n τ δ h ⊆ e5 K E δ) ≤
      (q.f6 n).prob (fun h=>∃ x,x ∈ iE K n τ δ h ∧ x ∉ e5 K E δ):=by
    apply aD.v7
    intro h hh
    by_contra hn
    apply hh
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  apply (hm.trans hu).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s:=Finset.univ) (fun x _=>hx x)
end
namespace aD
section
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} [Fintype Ω] [Fintype α]
lemma Dh {ι:Type c9} [Fintype ι] (P:ι → Prop) (f:ι → ℝ) :
    (∏ i,if P i then f i else 0) = if ∀ i,P i then ∏ i,f i else 0:=by
  by_cases h:∀ i,P i
  · simp [h]
  · rw [gR h]
    push Not at h
    obtain ⟨i,hi⟩:=h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (gR hi)
lemma Vc (p:aD Ω) (f:Ω → α) (n:ℕ) :
    (p.f6 n).map (fun x i=>f (x i)) = (p.map f).f6 n:=by
  apply aD.ext; rintro y
  simp only [f7,Mv]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Dh]
  congr 1
  exact propext funext_iff
lemma Dj (p:aD Ω) (E:Ω → Prop) (n:ℕ) :
    (p.f6 n).prob (fun x=>∀ i,E (x i)) = (p.prob E)^n:=by
  simp only [prob,Mv]
  calc
    _ = ∑ x:Fin n → Ω,∏ i,if E (x i) then p (x i) else 0:=by
      apply Finset.sum_congr rfl
      intro x _
      have h:=Dh (fun i=>E (x i)) (fun i=>p (x i))
      by_cases hh:∀ i,E (x i) <;> simpa only [hh,ite_true,ite_false] using h.symm
    _ = _:=by
      rw [← Fintype.prod_sum (fun (_:Fin n) (ω:Ω)=>if E ω then p ω else (0:ℝ))]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
lemma TU (p:aD Ω) (E F:Ω → Prop) (n:ℕ)
    (h:∀ x,E x → ¬ F x) :
    (p.f6 n).prob (fun x=>∀ i,E (x i)) ≤ (1-p.prob F)^n:=by
  rw [← p.pI F,← p.Dj]
  exact (p.f6 n).v7 (fun x hx i=>h _ (hx i))
lemma ME (p:aD Ω) (E:Ω → Prop) (n:ℕ) {c:ℝ}
    (hp:c ≤ 1-p.prob E) :
    (p.f6 n).prob (fun x=>∀ i,E (x i)) ≤ Real.exp (-(n:ℝ)*c):=by
  have hbase:p.prob E ≤ Real.exp (-c):=by
    have h:=Real.add_one_le_exp (-c)
    linarith only [hp,h]
  rw [Dj]
  calc
    _ ≤ (Real.exp (-c))^n:=pow_le_pow_left₀ (p.nZ E) hbase n
    _ = _:=by rw [← Real.exp_nat_mul]; congr 1; ring
lemma N4 (p:aD Ω) (f:Ω → α) (g:α → ℝ) :
    (∑ a,p.map f a*g a) = ∑ ω,p ω*g (f ω):=by
  simp only [f7,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  simp
lemma MJ (p:aD Ω) (q:Ω → aD α) (f:Ω → α → ℝ) :
    (∑ v,p.joint q v*f v.1 v.2) = ∑ ω,p ω*(∑ a,q ω a*f ω a):=by
  simp only [Fintype.sum_prod_type,jv,Finset.mul_sum,mul_assoc]
lemma Vk (p:aD Ω) (E:Ω → Prop) :
    p.map (fun ω=>decide (E ω)) true = p.prob E:=by
  simp only [f7,decide_eq_true_eq,prob]
lemma Lk (p:aD Ω) (f:Ω → ℝ)
    (hf:∀ ω,0 ≤ f ω) {c t:ℝ} (ht:0 < t)
    (hc:(∑ ω,p ω*f ω) ≤ c) :
    1-c/t ≤ p.prob (fun ω=>f ω ≤ t):=by
  have h:=(p.v8 f hf ht).trans ((div_le_div_iff_of_pos_right ht).mpr hc)
  have he:=p.pI (fun ω=>f ω ≤ t)
  simp only [not_le] at he
  linarith only [h,he]
end
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {β:Type dD} [Fintype Ω] [Fintype α] [Fintype β]
lemma Bj (p:aD Ω) (X Y:Ω → α) (E:Ω → Bool)
    (hE:∀ ω,p ω ≠ 0 → E ω = true → X ω=Y ω) :
    p.H X-p.H Y ≤ Real.binEntropy (p.map E true)+
      (1-p.map E true)*Real.log (Fintype.card α):=by
  have h:=p.Nt X Y (fun y=>{y}) E (b:=1) le_rfl (by
    intro ω hp he
    simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one,le_refl,and_true]
    exact hE ω hp he)
  rw [Real.log_one,mul_zero,add_zero] at h
  have hc:=p.Ot X Y
  linarith only [h,hc]
lemma Bk (p:aD Ω) (X X':Ω → α) (O O':Ω → β)
    (E:Ω → Bool) (hE:∀ ω,p ω ≠ 0 → E ω=true → X ω=X' ω ∧ O ω=O' ω) :
    p.g7 X O-p.g7 X' O' ≤ 2*Real.binEntropy (p.map E true)+
      (1-p.map E true)*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)):=by
  have h1:=p.Bj (fun ω=>(X ω,O ω)) (fun ω=>(X' ω,O' ω)) E
    (fun ω hp he=>Prod.ext (hE ω hp he).1 (hE ω hp he).2)
  have h2:=p.Bj O' O E (fun ω hp he=>(hE ω hp he).2.symm)
  have hn:=p.nonempty
  have ha:Nonempty α:=⟨X (Classical.arbitrary Ω)⟩
  have hb:Nonempty β:=⟨O (Classical.arbitrary Ω)⟩
  have hca:(Fintype.card α:ℝ) ≠ 0:=by exact_mod_cast Fintype.card_ne_zero
  have hcb:(Fintype.card β:ℝ) ≠ 0:=by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod,Nat.cast_mul,Real.log_mul hca hcb] at h1
  unfold g7
  linarith only [h1,h2]
lemma zG {a:ℝ} (ha:0 < a) (ha1:a ≤ 1) :
    Real.binEntropy a ≤ a*(1-Real.log a):=by
  have h:Real.negMulLog (1-a) ≤ a:=by
    by_cases hz:1-a=0
    · simp only [hz,Real.negMulLog_zero]
      exact ha.le
    · have hp:0 < 1-a:=lt_of_le_of_ne (by linarith) (Ne.symm hz)
      have hh:=Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
      rw [Real.log_inv] at hh
      have hm:=mul_le_mul_of_nonneg_left hh hp.le
      rw [mul_sub,mul_inv_cancel₀ hz,mul_one] at hm
      unfold Real.negMulLog
      nlinarith only [hm]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  dsimp only [Real.negMulLog] at h ⊢
  nlinarith only [h]
lemma Lm {ι:Type c9} [Fintype ι] (w:aD ι) (a:ι → ℝ)
    (ha:∀ i,a i ∈ Set.Icc (0:ℝ) 1) :
    (∑ i,w i*Real.binEntropy (a i)) ≤ Real.binEntropy (∑ i,w i*a i):=by
  exact Real.strictConcave_binEntropy.concaveOn.le_map_sum (fun i _=>w.nonneg i) w.dN (fun i _=>ha i)
end aD
open scoped BigOperators Classical
namespace aD
variable {Ω:Type bU} {Γ:Type gQ} {G:Type jY} [Fintype Ω] [Fintype Γ] [Fintype G] [AddCommGroup G]
omit [AddCommGroup G] in
lemma UC (p:aD G) (K:Finset G) :
    p.prob (fun x=>x ∈ K) = ∑ x ∈ K,p x:=by
  unfold prob
  calc
    _ = ∑ x ∈ K,if x ∈ K then p x else 0:=by
      symm
      convert! Finset.sum_subset (Finset.subset_univ K)
        (f:=fun x=>if x ∈ K then p x else (0:ℝ))
        (fun x _ hx=>gR hx) using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx:x∈K <;> simp only [hx,ite_true,ite_false]
    _ = _:=Finset.sum_congr rfl (fun x hx=>dO hx)
lemma EW (p:aD Ω) (q:Ω → aD Γ)
    (Bad:Ω → Prop) (E:Ω × Γ → Prop) {ε:ℝ} (hε:0 ≤ ε)
    (hg:∀ ω,¬ Bad ω → (q ω).prob (fun a=>E (ω,a)) ≤ ε) :
    (p.joint q).prob E ≤ p.prob Bad+ε:=by
  rw [pH]
  have h (ω:Ω):(q ω).prob (fun a=>E (ω,a)) ≤ (if Bad ω then 1 else 0)+ε:=by
    by_cases hb:Bad ω
    · simpa only [hb,ite_true] using (q ω).prob_le_one (fun a=>E (ω,a)) |>.trans (by linarith only [hε])
    · simpa only [hb,ite_false,zero_add] using hg ω hb
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  convert! hh using 1
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,p.dN,one_mul,prob]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp
omit [Fintype G] in
lemma Jm (p:aD Ω) (q:Ω → aD Γ)
    (Y:Ω → G) (h:Γ → G) (K:Finset G) (n:ℕ) :
    (∑ v,p.joint (fun ω=>(q ω).f6 n) v *
      (∑ i:Fin n,if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) =
      n*(p.joint q).prob (fun v=>Y v.1+h v.2 ∈ K):=by
  rw [MJ p (fun ω=>(q ω).f6 n)
    (fun ω v=>∑ i:Fin n,if Y ω+h (v i) ∈ K then (1:ℝ) else 0)]
  have he (i:Fin n) (ω:Ω) :
      (∑ v,(q ω).f6 n v*(if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        (q ω).prob (fun a=>Y ω+h a ∈ K):=by
    rw [← N4 ((q ω).f6 n) (fun v=>v i) (fun a=>if Y ω+h a ∈ K then (1:ℝ) else 0),
      Kk]
    unfold prob
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hh (ω:Ω) :
      (∑ v,(q ω).f6 n v*(∑ i:Fin n,if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        n*(q ω).prob (fun a=>Y ω+h a ∈ K):=by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [hh,mul_left_comm (p _) (n:ℝ)]
  rw [← Finset.mul_sum,pH p q (fun v=>Y v.1+h v.2∈K)]
lemma tA (p:aD Ω) (q:Ω → aD Γ)
    (Y:Ω → G) (h:Γ → G) (K:Finset G) (hK:K.Nonempty)
    {τ δ:ℝ} (hτ:0 ≤ τ) (hδ:0 < δ) {n:ℕ} (hn:0 < n)
    (hp:(p.joint q).prob (fun v=>Y v.1+h v.2 ∈ K) ≤
      τ*K.card/(Fintype.card G:ℝ)) :
    δ/(τ+δ) ≤ (p.joint (fun ω=>(q ω).f6 n)).prob
      (fun v=>Y v.1 ∈ iE K n τ δ (fun i=>h (v.2 i))):=by
  have hG:Nonempty G:=⟨Y (Classical.choice p.nonempty)⟩
  have hcard:(0:ℝ) < Fintype.card G:=by exact_mod_cast Fintype.card_pos
  have Zu:(0:ℝ) < K.card:=by exact_mod_cast Finset.card_pos.mpr hK
  have hnc:(0:ℝ) < n:=by exact_mod_cast hn
  have htd:0 < τ+δ:=by linarith
  have hb:(∑ v,p.joint (fun ω=>(q ω).f6 n) v *
      (∑ i:Fin n,if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) ≤
        n*(τ*K.card/(Fintype.card G:ℝ)):=by
    rw [Jm]
    exact mul_le_mul_of_nonneg_left hp hnc.le
  have hh:=(p.joint (fun ω=>(q ω).f6 n)).Lk
    (fun v=>∑ i:Fin n,if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)
    (fun _=>Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num))
    (t:=n*(τ+δ)*K.card/(Fintype.card G:ℝ)) (by positivity) hb
  have he:1-(n*(τ*K.card/(Fintype.card G:ℝ)))/(n*(τ+δ)*K.card/(Fintype.card G:ℝ)) =
      δ/(τ+δ):=by field_simp; ring
  rw [he] at hh
  simpa only [iE,Finset.mem_filter,Finset.mem_univ,true_and] using hh
lemma tB (p:aD Ω) (q:Ω → aD Γ)
    (h:Γ → G) (K:Finset G) (hK:K.Nonempty) (E:Ω → Finset G)
    (Bad:Ω → Prop) {τ δ ε b:ℝ}
    (hτ:0 ≤ τ) (hτ1:τ ≤ 3/8) (hδ:0 < δ) (hδ1:δ ≤ 1/64)
    (hε:0 ≤ ε) (n:ℕ)
    (hq:∀ ω,¬ Bad ω → ∀ y ∉ E ω,
      (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE:∀ ω,¬ Bad ω → ((E ω).card:ℝ)/δ ≤ b)
    (iJ:(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) ≤ ε) :
    (p.joint (fun ω=>(q ω).f6 n)).prob (fun v =>
      b < ((iE K n τ δ (fun i=>h (v.2 i))).card:ℝ)) ≤ p.prob Bad+ε:=by
  apply EW p _ Bad _ hε
  intro ω hg
  have ha:=(Lj ((q ω).map h) K (E ω) hK hτ hτ1 hδ hδ1 (hq ω hg) n).trans iJ
  rw [← Vc,oN] at ha
  apply (v7 _ ?_).trans ha
  intro x hx hs
  have hc:=Finset.card_le_card hs
  have hcR:((iE K n τ δ (fun i=>h (x i))).card:ℝ) ≤
      ((e5 K (E ω) δ).card:ℝ):=by exact_mod_cast hc
  have hb:=(DM K (E ω) hK hδ).trans (hE ω hg)
  linarith only [hx,hcR,hb]
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD dD c9 gQ jY
namespace GaussianMoat
open scoped BigOperators Classical
namespace aD
variable {Ω:Type bU} {α:Type cD} {β:Type dD} [Fintype Ω] [Fintype α] [Fintype β]
lemma sO (p:aD Ω) (X:Ω → α) (C:Ω → β)
    (L:β → Finset α) {b:ℝ} (hb:1 ≤ b) :
    let a:=p.prob (fun ω=>X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)
    a*(Real.log (Fintype.card α)-Real.log b)-Real.binEntropy a ≤
      Real.log (Fintype.card α)-p.bT X C:=by
  dsimp only
  have hh:=p.JM X C L
    (fun ω=>decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)) hb
    (fun ω _ he=>of_decide_eq_true he)
  have ha:(p.map (fun ω=>decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b))) true =
      p.prob (fun ω=>X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b):=by
    simp only [f7,decide_eq_true_eq,prob]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> rfl
  rw [ha] at hh
  simpa only [g7,← jW,bT] using hh
lemma EY {ι:Type c9} [Fintype ι] (w:aD ι)
    (a d:ι → ℝ) {a₀ v:ℝ} (ha:∀ i,a i ∈ Set.Icc (0:ℝ) 1)
    (ha₀:0 < a₀) (hav:a₀ ≤ ∑ i,w i*a i)
    (hv:2*(1-Real.log a₀) ≤ v)
    (hdef:∀ i,a i*v-Real.binEntropy (a i) ≤ d i) :
    a₀*v/2 ≤ ∑ i,w i*d i:=by
  let A:=∑ i,w i*a i
  have hA:0 < A:=lt_of_lt_of_le ha₀ hav
  have hA1:A ≤ 1:=by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (ha i).2 (w.nonneg i))
    simpa only [mul_one,w.dN] using hh
  have Yb:a₀ ≤ 1:=hav.trans hA1
  have hl:Real.log a₀ ≤ Real.log A:=Real.log_le_log ha₀ hav
  have hl0:Real.log a₀ ≤ 0:=Real.log_nonpos ha₀.le Yb
  have hv0:0 ≤ v:=by linarith only [hv,hl0]
  have hh:=w.Lm a ha
  have hp:=zG hA hA1
  have hdl:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hdef i) (w.nonneg i))
  rw [show (∑ i,w i*(a i*v-Real.binEntropy (a i))) =
      A*v-∑ i,w i*Real.binEntropy (a i) by
        simp only [mul_sub,Finset.sum_sub_distrib,← mul_assoc,← Finset.sum_mul,A]] at hdl
  have hlog:=mul_le_mul_of_nonneg_left hl hA.le
  have W2:=mul_le_mul_of_nonneg_left hv hA.le
  have ham:=mul_le_mul_of_nonneg_right hav hv0
  change (∑ i,w i*Real.binEntropy (a i)) ≤ Real.binEntropy A at hh
  nlinarith only [hdl,hh,hp,hlog,W2,ham]
theorem Cc {Γ:Type gQ} {G:Type jY} [Fintype Γ] [Fintype G] [AddCommGroup G]
    (p:aD Ω) (q:Ω → aD Γ) (Y:Ω → G) (h:Γ → G)
    (K:Finset G) (hK:K.Nonempty) (E:Ω → Finset G) (Bad:Ω → Prop)
    {τ δ ε b:ℝ} {n:ℕ} (hn:0<n)
    (hτ:0≤τ) (hτ1:τ≤3/8) (hδ:0<δ) (hδ1:δ≤1/64)
    (hε:0≤ε) (hb:1≤b)
    (hp:(p.joint q).prob (fun v=>Y v.1+h v.2∈K) ≤ τ*K.card/(Fintype.card G:ℝ))
    (hq:∀ ω,¬ Bad ω → ∀ y ∉ E ω,(τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE:∀ ω,¬ Bad ω → ((E ω).card:ℝ)/δ≤b)
    (iJ:(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ)))≤ε) :
    let P:=p.joint (fun ω=>(q ω).f6 n)
    let L:=fun v:Fin n → Γ=>iE K n τ δ (fun i=>h (v i))
    let a:=P.prob (fun v=>Y v.1 ∈ L v.2 ∧ ((L v.2).card:ℝ)≤b)
    δ/(τ+δ)-p.prob Bad-ε ≤ a ∧
      a*(Real.log (Fintype.card G)-Real.log b)-Real.binEntropy a ≤
        Real.log (Fintype.card G)-P.bT (fun v=>Y v.1) Prod.snd:=by
  dsimp only
  constructor
  · have sP:=p.tA q Y h K hK hτ hδ hn hp
    have hsize:=p.tB q h K hK E Bad hτ hτ1 hδ hδ1 hε n hq hE iJ
    have hi:=(p.joint (fun ω=>(q ω).f6 n)).Ip
      (fun v=>Y v.1 ∈ iE K n τ δ (fun i=>h (v.2 i)))
      (fun v=>((iE K n τ δ (fun i=>h (v.2 i))).card:ℝ)≤b)
    simp only [not_le] at hi
    linarith only [sP,hsize,hi]
  · exact sO (p.joint (fun ω=>(q ω).f6 n))
      (fun v=>Y v.1) Prod.snd
      (fun v=>iE K n τ δ (fun i=>h (v i))) hb
end aD
lemma Ln {ι:Type c9} [Fintype ι] [DecidableEq ι] (f:ι → ℝ) (i:ι) :
    (𝔼 π:Equiv.Perm ι,f (π i)) = 𝔼 j,f j:=by
  let:Nonempty ι:=⟨i⟩
  calc
    _ = 𝔼 j:ι,𝔼 π:Equiv.Perm ι,f (π j):=by
      rw [show (fun j:ι=>𝔼 π:Equiv.Perm ι,f (π j)) =
        (fun _=>𝔼 π:Equiv.Perm ι,f (π i)) by
          funext j; exact r8 f j i]
      simp only [Fintype.expect_const]
    _ = 𝔼 π:Equiv.Perm ι,𝔼 j:ι,f (π j):=Finset.expect_comm _ _ _
    _ = _:=by
      have he (π:Equiv.Perm ι):(𝔼 j,f (π j)) = 𝔼 j,f j :=
        Fintype.expect_equiv π _ _ (fun _=>rfl)
      simp only [he,Fintype.expect_const]
namespace aD
variable {Ω:Type bU} {α:Type cD} {β:Type dD} [Fintype Ω] {k:ℕ}
lemma Pz (p:aD Ω) (X:Ω → α) (Y:Ω → β) :
    p.Hf X-p.Hf Y ≤ p.bT X Y:=by
  have h:=p.kH Y X
  rw [p.kd Y X] at h
  exact sub_le_sub_right h _
lemma wc (p:aD Ω) (X:Ω → Fin k → α)
    (C:Ω → β) {b:ℕ} (hb:b ≤ k) :
    p.bF X b-p.Hf C ≤
      b*(𝔼 i:Fin k,p.bT (fun ω=>X ω i) C):=by
  have hh (π:Equiv.Perm (Fin k)) :
      p.Hf (aF X π b)-p.Hf C ≤
        ∑ i:Fin b,p.bT (fun ω=>X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C:=by
    apply (p.Pz _ C).trans
    apply (p.nQ _
      (fun ω (i:Fin b)=>X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C ?_).trans
      (p.l6 _ C)
    intro ω ν hx _
    funext i
    by_cases hi:i.val<b
    · simpa only [aF,hi,dO] using congrArg some (congrFun hx ⟨i.val,hi⟩)
    · simp only [aF,hi,ite_false]
  have hav:=Finset.expect_le_expect (s:=Finset.univ) (fun π _=>hh π)
  have he (i:Fin b) :
      (𝔼 π:Equiv.Perm (Fin k),p.bT (fun ω=>X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C) =
        𝔼 j:Fin k,p.bT (fun ω=>X ω j) C :=
    Ln (fun j=>p.bT (fun ω=>X ω j) C) _
  simpa only [bF,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.expect_sum_comm,he,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using hav
lemma w7 (p:aD Ω) (X:(Fin k → Bool) → Ω → Fin k → α)
    (C:Ω → β) {b:ℕ} (hb:b ≤ k) :
    p.gP X b-p.Hf C ≤
      b*(𝔼 σ:Fin k → Bool,𝔼 i:Fin k,p.bT (fun ω=>X σ ω i) C):=by
  have h:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    p.wc (X σ) C hb)
  simpa only [gP,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.mul_expect] using h
end aD
theorem aE.EZ {Ω:Type bU} {β:Type dD} [Fintype Ω]
    (s:aE) (p:aD Ω) (Y:Ω → GaussianInt) (C:Ω → β)
    {b:ℕ} (hb:b ≤ s.primes.card) :
    s.aV p Y b-p.Hf C ≤
      b*(𝔼 σ:Fin s.primes.card → Bool,𝔼 i:Fin s.primes.card,
        p.bT (fun ω=>s.bC σ (Y ω) i) C) :=
  p.w7 _ C hb
namespace aD
section
theorem DN {Ω:Type bU} {Γ:Type gQ} {ι:Type c9} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G:ι → Type jY) [∀ i,Fintype (G i)] [∀ i,AddCommGroup (G i)]
    (w:aD ι) (p:aD Ω) (q:Ω → aD Γ)
    (Y:(i:ι) → Ω → G i) (h:(i:ι) → Γ → G i)
    (p8:ι → Prop) (DQ:ι → Ω → Prop)
    (K:(i:ι) → Finset (G i)) (E:(i:ι) → Ω → Finset (G i))
    (b:ι → ℝ) {τ δ ε η η' e v:ℝ} {n:ℕ}
    (hn:0 < n) (hτ:0 ≤ τ) (hτ1:τ ≤ 3/8)
    (hδ:0 < δ) (hδ1:δ ≤ 1/64) (hε:0 ≤ ε) (hη:0 < η)
    (hnext:∑ i,w i*p.prob (DQ i) ≤ η')
    (jd:η'+ε ≤ η*δ/2)
    (jR:2*(1-Real.log (η*δ/2)) ≤ v)
    (jI:e < η*δ*v/4)
    (kC:(∑ i,w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω=>(q ω).f6 n)).bT (fun x=>Y i x.1) Prod.snd)) ≤ e)
    (hK:∀ i,p8 i → (K i).Nonempty)
    (hb:∀ i,p8 i → 1 ≤ b i)
    (hv:∀ i,p8 i → v ≤ Real.log (Fintype.card (G i))-Real.log (b i))
    (hp:∀ i,p8 i → (p.joint q).prob (fun x=>Y i x.1+h i x.2 ∈ K i) ≤
      τ*(K i).card/(Fintype.card (G i):ℝ))
    (hq:∀ i,p8 i → ∀ ω,¬DQ i ω → ∀ y ∉ E i ω,
      (τ+4*δ)/(Fintype.card (G i):ℝ) ≤ (q ω).map (h i) y)
    (hE:∀ i,p8 i → ∀ ω,¬DQ i ω → ((E i ω).card:ℝ)/δ ≤ b i)
    (iJ:∀ i,p8 i → (Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*(K i).card/(2*(Fintype.card (G i):ℝ))) ≤ ε) :
    w.prob p8 ≤ η:=by
  let P:=p.joint (fun ω=>(q ω).f6 n)
  let L:=fun i (x:Fin n → Γ)=>iE (K i) n τ δ (fun j=>h i (x j))
  let a:=fun i=>if p8 i then P.prob
    (fun x=>Y i x.1 ∈ L i x.2 ∧ ((L i x.2).card:ℝ) ≤ b i) else 0
  let d:=fun i=>Real.log (Fintype.card (G i))-P.bT (fun x=>Y i x.1) Prod.snd
  have hd (i:ι):0 ≤ d i:=by
    exact sub_nonneg.mpr ((P.C8 _ _).trans (P.kF _))
  have ha (i:ι):a i ∈ Set.Icc (0:ℝ) 1:=by
    dsimp only [a]
    split_ifs
    · exact ⟨P.nZ _,P.prob_le_one _⟩
    · norm_num
  have hstep (i:ι) (hi:p8 i) :
      δ-p.prob (DQ i)-ε ≤ a i ∧ a i*v-Real.binEntropy (a i) ≤ d i:=by
    have hh:=Cc p q (Y i) (h i) (K i) (hK i hi) (E i) (DQ i)
      hn hτ hτ1 hδ hδ1 hε (hb i hi) (hp i hi) (hq i hi) (hE i hi) (iJ i hi)
    dsimp only at hh
    have hh':δ/(τ+δ)-p.prob (DQ i)-ε ≤ a i ∧
        a i*(Real.log (Fintype.card (G i))-Real.log (b i))-Real.binEntropy (a i) ≤ d i:=by
      simpa only [a,hi,dO,P,L,d] using hh
    constructor
    · have htd:0 < τ+δ:=by linarith only [hτ,hδ]
      have Yc:τ+δ ≤ 1:=by linarith only [hτ1,hδ1]
      have hfrac:δ ≤ δ/(τ+δ):=(le_div_iff₀ htd).mpr (by nlinarith only [Yc,hδ])
      linarith only [hh'.1,hfrac]
    · have hm:=mul_le_mul_of_nonneg_left (hv i hi) (ha i).1
      linarith only [hh'.2,hm]
  have hl (i:ι):δ*(if p8 i then (1:ℝ) else 0)-p.prob (DQ i)-ε ≤ a i:=by
    by_cases hi:p8 i
    · simpa only [hi,ite_true,mul_one] using (hstep i hi).1
    · simp only [hi,ite_false,mul_zero,a]
      linarith only [p.nZ (DQ i),hε]
  have hdef (i:ι):a i*v-Real.binEntropy (a i) ≤ d i:=by
    by_cases hi:p8 i
    · exact (hstep i hi).2
    · simpa only [a,hi,ite_false,Real.binEntropy_zero,zero_mul,sub_zero] using hd i
  by_contra hc
  have YU:η < w.prob p8:=lt_of_not_ge hc
  have UF:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hl i) (w.nonneg i))
  have heq:(∑ i,w i*(δ*(if p8 i then (1:ℝ) else 0)-p.prob (DQ i)-ε)) =
      δ*w.prob p8-(∑ i,w i*p.prob (DQ i))-ε:=by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,w.dN,one_mul,prob,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq] at UF
  have hav:η*δ/2 ≤ ∑ i,w i*a i:=by
    have hm:=mul_le_mul_of_nonneg_left YU.le hδ.le
    linarith only [UF,hm,hnext,jd]
  have Yd:=EY w a d ha (by positivity:0 < η*δ/2) hav jR hdef
  change (∑ i,w i*d i) ≤ e at kC
  nlinarith only [Yd,kC,jI]
variable {Ω:Type bU} {G:Type jY} [Fintype Ω] [Fintype G]
theorem ML {ι:Type c9} [Fintype ι]
    (G:ι → Type jY) [∀ i,Fintype (G i)]
    (w:aD ι) (p:(i:ι) → aD (G i))
    (K:(i:ι) → Finset (G i)) (Bad:ι → Prop) {b e:ℝ}
    (hb:0 < b)
    (hK:∀ i,∀ x ∈ K i,p i x ≤ (3/8:ℝ)/(Fintype.card (G i):ℝ))
    (hbad:∀ i,Bad i → b ≤ ((K i).card:ℝ)/(8*(Fintype.card (G i):ℝ)))
    (hdef:(∑ i,w i*(Real.log (Fintype.card (G i))-(p i).entropy)) ≤ e) :
    w.prob Bad ≤ e/b:=by
  have h (i:ι):b*(if Bad i then (1:ℝ) else 0) ≤
      Real.log (Fintype.card (G i))-(p i).entropy:=by
    by_cases hi:Bad i
    · simp only [hi,ite_true,mul_one]
      exact (hbad i hi).trans ((p i).L7 (K i) (by
        intro x hx
        convert hK i x hx using 1; ring))
    · simp only [hi,ite_false,mul_zero]
      exact sub_nonneg.mpr (p i).lK
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (h i) (w.nonneg i))
  have he:(∑ i,w i*(b*(if Bad i then (1:ℝ) else 0)))=b*w.prob Bad:=by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he] at hs
  apply (le_div_iff₀ hb).mpr
  linarith only [hs,hdef]
end
variable {Ω:Type bU} {α:Type cD} {β:Type dD} [Fintype Ω] [Fintype α] [Fintype β]
lemma MO [Nonempty Ω] (e:Equiv.Perm Ω):(uniform Ω).map e = uniform Ω:=by
  apply aD.ext; rintro x
  rw [lA]
  rfl
lemma Qz (E:Ω → Prop) [Nonempty Ω] :
    (uniform Ω).prob E = ((Finset.univ.filter E).card:ℝ)/(Fintype.card Ω:ℝ):=by
  simp only [prob,m4,div_eq_mul_inv]
  rw [← Finset.sum_boole]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp
lemma Dk (n a:ℕ) (ha:a ≤ n+1) :
    (uniform (Fin (n+1))).prob (fun i=>i.val+a<n+1) = 1-(a:ℝ)/(n+1):=by
  rw [Qz]
  have he:(Finset.univ.filter (fun i:Fin (n+1)=>i.val+a<n+1)) =
      Finset.univ.filter (fun i:Fin (n+1)=>i.val<n+1-a):=by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hcard:(Finset.univ.filter (fun i:Fin (n+1)=>i.val+a<n+1)).card = n+1-a:=by
    rw [he,Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]
  calc
    _ = ((n+1-a:ℕ):ℝ)/(n+1):=by
      congr 1
      · convert! congrArg (fun k:ℕ=>(k:ℝ)) hcard using 1
        congr 2
        ext i
        simp
      · simp
    _ = _:=by
      rw [Nat.cast_sub ha,Nat.cast_add,Nat.cast_one]
      field_simp
lemma yP (p:aD Ω) {Γ:Type gQ} [Fintype Γ] [Nonempty Γ]
    (e:Equiv.Perm Γ) :
    (p.joint (fun _=>uniform Γ)).map (fun v=>(v.1,e v.2)) = p.joint (fun _=>uniform Γ):=by
  have h:=ow p (fun _=>uniform Γ) (fun _ v=>e v)
  simpa only [MO] using h
lemma OH (p:aD Ω) (t:Ω → ℕ) (n a:ℕ) (ha:a≤n)
    (E:ℕ → Prop) :
    (p.joint (fun _=>uniform (Fin (n+1)))).prob (fun v=>E (t v.1+v.2.val)) ≤
      (p.joint (fun _=>uniform (Fin (n+1)))).prob (fun v=>E (t v.1+v.2.val+a))+
        (a:ℝ)/(n+1):=by
  let e:Equiv.Perm (Fin (n+1)):=Equiv.addRight ⟨a,by omega⟩
  let P:=p.joint (fun _=>uniform (Fin (n+1)))
  have ND:P.prob (fun v=>E (t v.1+(e v.2).val)) =
      P.prob (fun v=>E (t v.1+v.2.val)):=by
    have hh:=congrArg (fun Q:aD (Ω × Fin (n+1))=>Q.prob
      (fun v=>E (t v.1+v.2.val))) (p.yP e)
    simpa only [oN] using hh
  have W3:P.prob (fun v=>v.2.val+a<n+1) = 1-(a:ℝ)/(n+1):=by
    rw [pH]
    simp only [Dk n a (by omega),← Finset.sum_mul,p.dN,one_mul]
  have hE:P.prob (fun v=>E (t v.1+(e v.2).val) ∧ v.2.val+a<n+1) ≤
      P.prob (fun v=>E (t v.1+v.2.val+a)):=by
    apply P.v7
    intro v hv
    have he:(e v.2).val = v.2.val+a:=by
      change (v.2+(⟨a,by omega⟩:Fin (n+1))).val = _
      exact Fin.val_add_eq_of_add_lt hv.2
    simpa only [he,Nat.add_assoc] using hv.1
  have hh:=P.Ip (fun v=>E (t v.1+(e v.2).val)) (fun v=>v.2.val+a<n+1)
  have hc:=P.pI (fun v=>v.2.val+a<n+1)
  rw [W3] at hc
  rw [ND] at hh
  linarith only [hE,hh,hc]
lemma N5 (p:aD Ω) (t:Ω → ℕ) (n a:ℕ) (ha:a≤n)
    (X:ℕ → α) (C:ℕ → β) :
    (p.joint (fun _=>uniform (Fin (n+1)))).g7
      (fun v=>X (t v.1+v.2.val+a)) (fun v=>C (t v.1+v.2.val+a)) ≤
    (p.joint (fun _=>uniform (Fin (n+1)))).g7
      (fun v=>X (t v.1+v.2.val)) (fun v=>C (t v.1+v.2.val)) +
      2*Real.binEntropy ((a:ℝ)/(n+1))+
        ((a:ℝ)/(n+1))*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)):=by
  let e:Equiv.Perm (Fin (n+1)):=Equiv.addRight ⟨a,by omega⟩
  let P:=p.joint (fun _=>uniform (Fin (n+1)))
  let good:=fun v:Ω × Fin (n+1)=>decide (v.2.val+a<n+1)
  have hm:P.map good true=1-(a:ℝ)/(n+1):=by
    have hh:P.map good true=P.prob (fun v=>v.2.val+a<n+1):=by
      simp only [f7,good,prob,decide_eq_true_eq]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    rw [hh,pH]
    simp only [Dk n a (by omega),
      ← Finset.sum_mul,p.dN,one_mul]
  have he:P.g7 (fun v=>X (t v.1+(e v.2).val)) (fun v=>C (t v.1+(e v.2).val)) =
      P.g7 (fun v=>X (t v.1+v.2.val)) (fun v=>C (t v.1+v.2.val)):=by
    have hh:=congrArg (fun Q:aD (Ω × Fin (n+1)) =>
      Q.g7 (fun v=>X (t v.1+v.2.val)) (fun v=>C (t v.1+v.2.val))) (p.yP e)
    simpa only [g7,WO,Function.comp_def] using hh
  have h:=P.Bk
    (fun v=>X (t v.1+v.2.val+a)) (fun v=>X (t v.1+(e v.2).val))
    (fun v=>C (t v.1+v.2.val+a)) (fun v=>C (t v.1+(e v.2).val)) good (by
      intro v _ hv
      have hlt:v.2.val+a<n+1:=of_decide_eq_true hv
      have hev:(e v.2).val=v.2.val+a:=Fin.val_add_eq_of_add_lt hlt
      simp only [hev,Nat.add_assoc,and_self])
  rw [hm,he,Real.binEntropy_one_sub] at h
  linarith only [h]
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD gQ jY c9 dD g4
namespace GaussianMoat
namespace aD
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {Γ:Type gQ} {G:Type jY} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]
lemma OI (p:aD Ω) (A B:Ω → Prop) :
    p.prob (fun ω=>A ω ∧ B ω)+p.prob (fun ω=>A ω ∧ ¬B ω)=p.prob A:=by
  simp only [prob,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha:A ω <;> by_cases hb:B ω <;> simp [ha,hb]
lemma TW (p:aD Ω) (q:Ω → aD Γ) (E:Γ → Prop) :
    (p.mix q).prob E = ∑ ω,p ω*(q ω).prob E:=by
  rw [← qN,oN,pH]
lemma E0 (p:aD Ω) (C:Ω → α) (Bad:Ω → Prop) :
    (p.map C).prob (fun a=>(1/2:ℝ)<(p.eO C a).prob Bad) ≤ 2*p.prob Bad:=by
  have h:=(p.map C).v8 (fun a=>(p.eO C a).prob Bad)
    (fun a=>(p.eO C a).nZ _) (by norm_num:(0:ℝ)<1/2)
  rw [p.Mw] at h
  linarith only [h]
lemma Gv (p:aD Ω) (Good:Ω → Prop) (E:Ω → Finset G)
    {e:ℝ} (he:0≤e) (hE:∀ ω,Good ω → ((E ω).card:ℝ)≤e)
    (hG:(1/2:ℝ)≤p.prob Good) :
    ((Finset.univ.filter (fun x:G =>
      p.prob (fun ω=>Good ω ∧ x∉E ω)<1/4)).card:ℝ) ≤ 4*e:=by
  let u:=fun x=>p.prob (fun ω=>Good ω ∧ x∉E ω)
  let f:=fun x=>p.prob (fun ω=>Good ω ∧ x∈E ω)
  let K:=Finset.univ.filter (fun x:G=>u x<1/4)
  have hsum:(∑ x:G,f x) ≤ e:=by
    simp only [f,prob]
    rw [Finset.sum_comm]
    have hh (ω:Ω):(∑ x:G,if Good ω ∧ x∈E ω then p ω else 0) ≤ p ω*e:=by
      by_cases hg:Good ω
      · have hc:(∑ x:G,if Good ω ∧ x∈E ω then p ω else 0) = p ω*(E ω).card:=by
          simp only [hg,true_and]
          calc
            _ = ∑ x:G,p ω*(if x∈E ω then (1:ℝ) else 0):=by
              apply Finset.sum_congr rfl
              intro x _
              split_ifs <;> simp
            _ = _:=by rw [← Finset.mul_sum]; simp
        rw [hc]
        exact mul_le_mul_of_nonneg_left (hE ω hg) (p.nonneg ω)
      · simp only [hg,false_and,ite_false,Finset.sum_const_zero]
        exact mul_nonneg (p.nonneg ω) he
    have ht:=Finset.sum_le_sum (s:=Finset.univ) (fun ω _=>hh ω)
    simp only [← Finset.sum_mul,p.dN,one_mul] at ht
    refine le_of_eq_of_le ?_ ht
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  have hk (x:G) (hx:x∈K):(1/4:ℝ)≤f x:=by
    have h:=p.OI Good (fun ω=>x∈E ω)
    have hu:u x<1/4:=(Finset.mem_filter.mp hx).2
    change f x+u x=p.prob Good at h
    linarith only [hu,h,hG]
  have hl:(K.card:ℝ)/4 ≤ ∑ x∈K,f x:=by
    have h:=Finset.sum_le_sum (s:=K) (fun x hx=>hk x hx)
    simpa only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul] using h
  have hr:(∑ x∈K,f x) ≤ ∑ x:G,f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
      (fun x _ _=>p.nZ _)
  change (K.card:ℝ)≤4*e
  linarith only [hl,hr,hsum]
omit [Fintype G] in
lemma Rd (p:aD Ω) (q:Ω → aD Γ) (Good:Ω → Prop)
    (E:Ω → Finset G) (hit:Γ → G → Prop) {τ:ℝ} (hτ:0≤τ)
    (hq:∀ ω,Good ω → ∀ x∉E ω,τ≤(q ω).prob (fun v=>hit v x))
    (x:G) (hx:(1/4:ℝ)≤p.prob (fun ω=>Good ω ∧ x∉E ω)) :
    τ/4 ≤ (p.mix q).prob (fun v=>hit v x):=by
  rw [TW]
  have h (ω:Ω):τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0) ≤ (q ω).prob (fun v=>hit v x):=by
    by_cases hg:Good ω ∧ x∉E ω
    · rw [dO hg,mul_one]
      exact hq ω hg.1 x hg.2
    · rw [gR hg,mul_zero]
      exact (q ω).nZ _
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  have he:(∑ ω,p ω*(τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0))) =
      τ*p.prob (fun ω=>Good ω ∧ x∉E ω):=by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [he] at hh
  have hm:=mul_le_mul_of_nonneg_left hx hτ
  linarith only [hh,hm]
lemma wA {ι:Type c9} [Fintype ι]
    (p:aD Ω) (E:ι → Ω → Prop)
    (h:∀ ω i j,E i ω → E j ω → i=j) :
    p.prob (fun ω=>∃ i,E i ω) = ∑ i,p.prob (E i):=by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he:∃ i,E i ω
  · obtain ⟨i,hi⟩:=he
    rw [dO ⟨i,hi⟩,Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      exact gR (fun hj=>hji (h ω j i hj hi))
    · simp
  · simp only [gR he]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact gR (fun hi=>he ⟨i,hi⟩)
end aD
section
namespace aD
open scoped BigOperators Classical
variable {Ω:Type bU} {ι:Type c9} {α:Type cD} {β:Type dD} {γ:Type g4} [Fintype Ω] [Fintype ι] [Fintype α] [Fintype β]
lemma R5 (p:aD Ω):p.Hf id = p.entropy:=by rw [jW,H,map_id]
lemma Iq (p:aD ι) (q:ι → aD Ω) (X:ι → Ω → γ) :
    (p.joint q).bT (fun v=>X v.1 v.2) Prod.fst = ∑ i,p i*(q i).Hf (X i):=by
  unfold bT
  rw [kd,oL]
  have h:=(p.joint q).NG Prod.fst id
  rw [qM,R5] at h
  change p.entropy = (p.joint q).Hf Prod.fst at h
  rw [← h]
  ring
lemma OJ (p:aD ι) (q:ι → aD Ω) (n:ℕ) (i:Fin n) :
    (p.joint (fun a=>(q a).f6 n)).map (fun v=>(v.1,v.2 i)) = p.joint q:=by
  calc
    _ = p.joint (fun a=>((q a).f6 n).map (fun x:Fin n → Ω=>x i)) :=
      A8 p (fun a=>(q a).f6 n) (fun x:Fin n → Ω=>x i)
    _ = _:=by simp only [Kk]
theorem wB (p:aD (α × β)) (q:α × β → aD Ω) (n:ℕ) :
    (p.joint (fun a=>(q a).f6 n)).i7 (fun v=>v.1.2) Prod.snd (fun v=>v.1.1) ≤
      (n:ℝ)*(p.joint q).i7 (fun v=>v.1.2) Prod.snd (fun v=>v.1.1):=by
  let P:=p.joint (fun a=>(q a).f6 n)
  let Q:=p.joint q
  have hsub:=P.l6 Prod.snd (fun v=>v.1.1)
  have W5 (i:Fin n):P.bT (fun v=>v.2 i) (fun v=>v.1.1) =
      Q.bT Prod.snd (fun v=>v.1.1):=by
    have h:=P.vh (fun v=>(v.1,v.2 i)) Prod.snd (fun v=>v.1.1)
    rw [OJ] at h
    exact h.symm
  simp only [W5,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsub
  have hcond:P.bT Prod.snd (fun v=>(v.1.1,v.1.2)) =
      (n:ℝ)*Q.bT Prod.snd (fun v=>(v.1.1,v.1.2)):=by
    change P.bT Prod.snd Prod.fst = (n:ℝ)*Q.bT Prod.snd Prod.fst
    rw [Iq p (fun a=>(q a).f6 n) (fun _ x=>x),
      Iq p q (fun _ x=>x)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    change p a*((q a).f6 n).Hf id = (n:ℝ)*(p a*(q a).Hf id)
    rw [R5,R5,Ra]
    ring
  change P.i7 _ _ _ ≤ (n:ℝ)*Q.i7 _ _ _
  rw [P.oO,Q.oO]
  unfold i7
  rw [hcond]
  nlinarith only [hsub]
end aD
open scoped BigOperators Classical
namespace aD
variable {Ω:Type bU} {α:Type cD} {Γ:Type gQ} {G:Type jY} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]
noncomputable def d9 (hit:Γ → G → Prop) (n:ℕ) (v:Fin n → Γ):Finset G :=
  Finset.univ.filter (fun x=>∀ i,¬ hit (v i) x)
lemma Cd (q:aD Γ) (hit:Γ → G → Prop)
    (E:Finset G) {c:ℝ} (QC:∀ x ∉ E,c≤q.prob (fun v=>hit v x)) (n:ℕ) :
    (∑ v,q.f6 n v*((d9 hit n v).card:ℝ)) ≤
      (E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c):=by
  have ND (x:G) (hx:x ∉ E) :
      (q.f6 n).prob (fun v=>x∈d9 hit n v) ≤ Real.exp (-(n:ℝ)*c):=by
    have hh:=q.ME (fun v=>¬hit v x) n (c:=c) (by
      rw [q.pI]; linarith only [QC x hx])
    simpa only [d9,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have he:(∑ v,q.f6 n v*((d9 hit n v).card:ℝ)) =
      ∑ x:G,(q.f6 n).prob (fun v=>x∈d9 hit n v):=by
    have hc (v:Fin n → Γ):((d9 hit n v).card:ℝ) =
        ∑ x:G,if x∈d9 hit n v then (1:ℝ) else 0:=by simp
    simp only [hc,Finset.mul_sum,prob]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hx:x∈d9 hit n v <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  rw [he]
  have hh (x:G):(q.f6 n).prob (fun v=>x∈d9 hit n v) ≤
      (if x∈E then (1:ℝ) else 0)+Real.exp (-(n:ℝ)*c):=by
    by_cases hx:x∈E
    · simp only [hx,ite_true]
      exact ((q.f6 n).prob_le_one _).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · simp only [hx,ite_false,zero_add]
      exact ND x hx
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun x _=>hh x)
  simpa only [Finset.sum_add_distrib,Finset.sum_boole,Finset.filter_mem_eq_inter,
    Finset.univ_inter,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs
lemma qU (q:aD Γ) (hit:Γ → G → Prop) (x:G)
    (h:∀ v,q v≠0 → ¬hit v x) (n:ℕ) :
    ∀ v,q.f6 n v≠0 → x∈d9 hit n v:=by
  intro v hv
  simp only [d9,Finset.mem_filter,Finset.mem_univ,true_and]
  intro i
  apply h
  intro hz
  apply hv
  change (∏ j:Fin n,q (v j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz
lemma Bl (p:aD Ω) (f:Ω → ℝ)
    (hf:∀ ω,p ω≠0 → 0<f ω) :
    (∑ ω,p ω*Real.log (f ω)) ≤ Real.log (∑ ω,p ω*f ω):=by
  let f':=fun ω=>if p ω=0 then (1:ℝ) else f ω
  have hh:=strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun ω _=>p.nonneg ω) p.dN (fun ω _=>show 0<f' ω from by
      dsimp only [f']; split_ifs with hz; norm_num; exact hf ω hz)
  have he (ω:Ω):p ω*f' ω=p ω*f ω:=by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  have hl (ω:Ω):p ω*Real.log (f' ω)=p ω*Real.log (f ω):=by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  simpa only [smul_eq_mul,he,hl] using hh
lemma tD (q:aD Γ) (hit:Γ → G → Prop)
    (x:G) (sP:∀ v,q v≠0 → ¬hit v x)
    (E:Finset G) {c:ℝ} (QC:∀ y ∉ E,c≤q.prob (fun v=>hit v y)) (n:ℕ) :
    (∑ v,q.f6 n v*Real.log (d9 hit n v).card) ≤
      Real.log ((E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c)):=by
  have hp (v:Fin n → Γ) (hv:q.f6 n v≠0):(0:ℝ)<(d9 hit n v).card:=by
    exact_mod_cast Finset.card_pos.mpr ⟨x,q.qU hit x sP n v hv⟩
  apply ((q.f6 n).Bl (fun v=>((d9 hit n v).card:ℝ)) hp).trans
  apply Real.log_le_log ?_ (q.Cd hit E QC n)
  have hex:∃ v,0 < q.f6 n v:=by
    by_contra hh
    push Not at hh
    have hz:∀ v,q.f6 n v=0:=fun v=>le_antisymm (hh v) ((q.f6 n).nonneg v)
    have hs:=(q.f6 n).dN
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨v,hv⟩:=hex
  exact Finset.sum_pos' (fun v _=>mul_nonneg ((q.f6 n).nonneg v) (Nat.cast_nonneg _))
    ⟨v,Finset.mem_univ v,mul_pos hv (hp v hv.ne')⟩
lemma wC (p:aD Ω) (X:Ω → G) (C:Ω → α)
    (hit:α → G → Prop) (hs:∀ ω,p ω≠0 → ¬hit (C ω) (X ω)) :
    p.bT X C ≤ ∑ a,p.map C a*Real.log ((Finset.univ.filter (fun x=>¬hit a x)).card):=by
  have h:=p.z9 X C (fun a=>Finset.univ.filter (fun x=>¬hit a x)) (by
    intro ω hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs ω hw)
  simpa only [g7,← jW,bT] using h
end aD
end
namespace aD
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} [Fintype Ω]
lemma N6 (p:aD Ω) {n k:ℕ} (X:Ω → Fin n → α)
    (C:Ω → β) (hk:k<n) :
    p.bT (aF X (Equiv.refl _) (k+1)) C =
      p.bT (aF X (Equiv.refl _) k) C+
        p.bT (fun ω=>X ω ⟨k,hk⟩) (fun ω=>(aF X (Equiv.refl _) k ω,C ω)):=by
  have he:p.bT (aF X (Equiv.refl _) (k+1)) C =
      p.bT (fun ω=>(aF X (Equiv.refl _) k ω,X ω ⟨k,hk⟩)) C:=by
    apply p.lC
    intro ω ν _
    constructor
    · intro h
      refine Prod.ext ?_ ?_
      · funext i
        by_cases hi:i.val<k
        · simpa only [aF,hi,dO,show i.val<k+1 by omega] using congrFun h i
        · simp [aF,hi]
      · simpa [aF] using congrFun h ⟨k,hk⟩
    · intro h
      funext i
      by_cases hi:i.val<k
      · simpa only [aF,hi,dO,show i.val<k+1 by omega] using
          congrFun (congrArg Prod.fst h) i
      · by_cases YV:i.val=k
        · have hi':i=⟨k,hk⟩:=Fin.ext YV
          subst i
          simpa [aF] using congrArg some (congrArg Prod.snd h)
        · simp [aF,show ¬i.val<k+1 by omega]
  rw [he,p.vT]
lemma PN (p:aD Ω) {n:ℕ} (X:Ω → Fin n → α)
    (C:Ω → β) (S:Fin n → Ω → γ)
    (hS:∀ i ω ν,aF X (Equiv.refl _) i.val ω=aF X (Equiv.refl _) i.val ν →
      C ω=C ν → S i ω=S i ν) :
    p.bT X C ≤ ∑ i:Fin n,p.bT (fun ω=>X ω i) (S i):=by
  have h (k:ℕ) (hk:k≤n):p.bT (aF X (Equiv.refl _) k) C ≤
      ∑ i:Fin k,p.bT (fun ω=>X ω ⟨i.val,by omega⟩) (S ⟨i.val,by omega⟩):=by
    induction k with
    | zero =>
      have he:p.bT (aF X (Equiv.refl _) 0) C = 0:=by
        unfold bT
        have hh:p.Hf (fun ω=>(aF X (Equiv.refl _) 0 ω,C ω)) = p.Hf C:=by
          apply p.aZ
          intro ω ν
          simp only [Oy,Prod.mk.injEq,true_and]
        rw [hh,sub_self]
      simp only [he,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
    | succ k ih =>
      rw [p.N6 X C (by omega),Fin.sum_univ_castSucc]
      have hm:=p.jL (fun ω=>X ω ⟨k,by omega⟩)
        (fun ω=>(aF X (Equiv.refl _) k ω,C ω)) (S ⟨k,by omega⟩)
        (fun ω ν hh=>hS ⟨k,by omega⟩ ω ν (congrArg Prod.fst hh) (congrArg Prod.snd hh))
      exact add_le_add (ih (by omega)) hm
  have he:p.bT (aF X (Equiv.refl _) n) C=p.bT X C:=by
    apply p.lC
    intro ω ν _
    constructor
    · intro h
      funext i
      simpa [aF,i.isLt] using congrFun h i
    · intro h
      funext i
      simp only [aF,i.isLt,dO,Equiv.refl_apply]
      exact congrArg some (congrFun h i)
  simpa only [he] using h n le_rfl
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9 bU cD dD g4 oG
namespace GaussianMoat
open scoped BigOperators Classical
noncomputable def cw (z:ℕ → GaussianInt) (L t:ℕ):Fin L → GaussianInt :=
  fun i=>z (t+i.val+1)-z (t+i.val)
lemma p9 (z:ℕ → GaussianInt) (L t:ℕ) :
    ∑ i,cw z L t i=z (t+L)-z t:=by
  simp only [cw]
  rw [Fin.sum_univ_eq_sum_range (fun i=>z (t+i+1)-z (t+i))]
  simpa only [Nat.add_assoc,Nat.add_zero] using
    Finset.sum_range_sub (fun i=>z (t+i)) L
lemma Kr (z:ℕ → GaussianInt) (L k t u:ℕ)
    (h:∀ j<k,cw z L (t+j*L)=cw z L (u+j*L)) :
    z (t+k*L)-z t=z (u+k*L)-z u:=by
  induction k with
  | zero=>simp
  | succ k ih =>
    have hh:=ih (fun j hj=>h j (by omega))
    have hk:=congrArg (fun w:Fin L → GaussianInt=>∑ i,w i) (h k (by omega))
    rw [p9,p9] at hk
    have ht:t+k*L+L=t+(k+1)*L:=by ring
    have hu:u+k*L+L=u+(k+1)*L:=by ring
    rw [ht,hu] at hk
    linear_combination hh+hk
lemma Gw {ι:Type c9} (f:ι → GaussianInt) (z:ℕ → GaussianInt)
    (L k t u:ℕ)
    (hQ:(fun i=>aR (f i) (z t))=(fun i=>aR (f i) (z u)))
    (hW:∀ j<k,cw z L (t+j*L)=cw z L (u+j*L)) :
    (fun i=>aR (f i) (z (t+k*L)))=
      (fun i=>aR (f i) (z (u+k*L))):=by
  have hd:=Kr z L k t u hW
  funext i
  have hh:=Da (congrFun hQ i) (congrArg (aR (f i)) hd)
  simpa only [add_sub_cancel] using hh
theorem vq {Ω:Type bU} {ι:Type c9} [Fintype Ω]
    (p:aD Ω) (t:Ω → ℕ) (z:ℕ → GaussianInt) (f:ι → GaussianInt)
    (L n:ℕ) (hL:0<L) :
    p.bT (fun ω=>cw z (n*L) (t ω))
      (fun ω i=>aR (f i) (z (t ω))) ≤
      ∑ j:Fin n,p.bT (fun ω=>cw z L (t ω+j.val*L))
        (fun ω i=>aR (f i) (z (t ω+j.val*L))):=by
  let W:=fun ω (j:Fin n)=>cw z L (t ω+j.val*L)
  let Q:=fun ω i=>aR (f i) (z (t ω))
  have hvec:p.bT (fun ω=>cw z (n*L) (t ω)) Q ≤ p.bT W Q:=by
    apply p.nQ
    intro ω ν h _
    funext i
    let j:Fin n:=⟨i.val/L,(Nat.div_lt_iff_lt_mul hL).mpr i.isLt⟩
    let a:Fin L:=⟨i.val%L,Nat.mod_lt _ hL⟩
    have hh:=congrFun (congrFun h j) a
    have he:j.val*L+a.val=i.val:=by
      dsimp only [j,a]
      simpa only [Nat.mul_comm] using Nat.div_add_mod i.val L
    simpa only [W,cw,Nat.add_assoc,he] using hh
  apply hvec.trans
  apply p.PN W Q
  intro j ω ν hW hQ
  apply Gw f z L j.val (t ω) (t ν) hQ
  intro k hk
  have hh:=congrFun hW ⟨k,lt_trans hk j.isLt⟩
  simpa only [aD.aF,Equiv.refl_apply,hk,dO,Option.some.injEq,W] using hh
noncomputable def kO (z:ℕ → GaussianInt) {D:ℝ}
    (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (L t:ℕ):Fin L → bY D :=
  fun i=>⟨cw z L t i,by
    rw [lZ]
    simpa only [cw,map_sub,← dist_eq_norm,dist_comm] using hz (t+i.val)⟩
lemma oR (z:ℕ → GaussianInt) {D:ℝ}
    (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (L t u:ℕ) :
    kO z hz L t=kO z hz L u ↔ cw z L t=cw z L u:=by
  constructor
  · intro h
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro h
    funext i
    exact Subtype.ext (congrFun h i)
lemma DU {Ω:Type bU} [Fintype Ω] (p:aD Ω) (t:Ω → ℕ)
    (z:ℕ → GaussianInt) {D:ℝ} (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (L:ℕ) :
    p.Hf (fun ω=>cw z L (t ω)) ≤ (L:ℝ)*Real.log (bY D).card:=by
  have he:p.Hf (fun ω=>cw z L (t ω))=p.Hf (fun ω=>kO z hz L (t ω)):=by
    apply p.aZ
    intro ω ν
    exact (oR z hz L (t ω) (t ν)).symm
  rw [he]
  have h:=p.kF (fun ω=>kO z hz L (t ω))
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] using h
@[simp] lemma Jp (π z w:GaussianInt) :
    aY π (z+w)=aY π z+aY π w:=rfl
@[simp] lemma lP (π z w:GaussianInt) :
    aY π (z-w)=aY π z-aY π w:=rfl
@[simp] lemma Gz (π:GaussianInt):aY π 0=0:=rfl
lemma wD (π:GaussianInt) (z:ℕ → GaussianInt)
    (hz:Function.Injective z) {D:ℝ} (hD:0 ≤ D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {L:ℕ}
    (j6:(D*L)^2 < (π.norm:ℝ)) (a t:ℕ)
    (x:GaussianInt ⧸ multiples π) (i j:Fin L)
    (hi:aY π (z (t+i.val)-z a)=x)
    (hj:aY π (z (t+j.val)-z a)=x):i=j:=by
  by_contra hij
  have hneq:z (t+i.val)≠z (t+j.val):=by
    intro he
    have ht:=hz he
    apply hij
    apply Fin.ext
    omega
  have hh:=g8 z hD hs t L i.val j.val (by omega) (by omega)
  rw [GaussianInt.toComplex_sub,← dist_eq_norm] at hh
  have hd:dist (z (t+i.val):ℂ) (z (t+j.val):ℂ)^2 < (π.norm:ℝ):=by
    exact (sq_le_sq₀ dist_nonneg (mul_nonneg hD (Nat.cast_nonneg L))).mpr hh |>.trans_lt j6
  have hres:aY π (z (t+i.val))=aY π (z (t+j.val)):=by
    simpa only [lP,sub_left_inj] using hi.trans hj.symm
  exact yT hneq hd ((jX _ _ _).mp hres)
lemma DX {Ω:Type bU} [Fintype Ω] (p:aD Ω)
    (π:GaussianInt) (z:ℕ → GaussianInt) (hz:Function.Injective z)
    {D:ℝ} (hD:0 ≤ D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    {L:ℕ} (j6:(D*L)^2 < (π.norm:ℝ)) (a:ℕ) (t:Ω → ℕ)
    (x:GaussianInt ⧸ multiples π) :
    p.prob (fun ω=>∃ i:Fin L,aY π (z (t ω+i.val)-z a)=x) =
      ∑ i:Fin L,p.prob (fun ω=>aY π (z (t ω+i.val)-z a)=x):=by
  apply p.wA
  intro ω i j hi hj
  exact wD π z hz hD hs j6 a (t ω) x i j hi hj
theorem w8 {Ω:Type bU} [Fintype Ω] (p:aD Ω)
    (π:GaussianInt) (z:ℕ → GaussianInt) (hz:Function.Injective z)
    {D c:ℝ} (hD:0 ≤ D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    {L N:ℕ} (j6:(D*L)^2 < (π.norm:ℝ)) (LI:L ≤ N)
    (iJ:(L:ℝ)/(N+1) ≤ c/2) (a:ℕ) (t:Ω → ℕ)
    (x:GaussianInt ⧸ multiples π)
    (hfloor:c ≤ (p.joint (fun _=>aD.uniform (Fin (N+1)))).prob
      (fun v=>aY π (z (t v.1+v.2.val)-z a)=x)) :
    (L:ℝ)*c/2 ≤ (p.joint (fun _=>aD.uniform (Fin (N+1)))).prob
      (fun v=>∃ i:Fin L,aY π (z (t v.1+v.2.val+i.val)-z a)=x):=by
  rw [DX _ π z hz hD hs j6 a]
  have hh (i:Fin L):c/2 ≤
      (p.joint (fun _=>aD.uniform (Fin (N+1)))).prob
        (fun v=>aY π (z (t v.1+v.2.val+i.val)-z a)=x):=by
    have hp:=p.OH t N i.val (by omega)
      (fun b=>aY π (z b-z a)=x)
    have he:(i.val:ℝ)/(N+1) ≤ c/2:=by
      apply le_trans _ iJ
      exact div_le_div_of_nonneg_right (by exact_mod_cast i.isLt.le) (by positivity)
    linarith only [hp,hfloor,he]
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hh i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc] using h
lemma Jq (π:GaussianInt) (z:ℕ → GaussianInt)
    (QD:∀ t,¬π ∣ z t) (a t L:ℕ) :
    ¬∃ i:Fin L,aY π (z (t+i.val)-z a) = -aY π (z a):=by
  rintro ⟨i,hi⟩
  have hh:aY π (z (t+i.val))=aY π 0:=by
    rw [lP] at hi
    rw [Gz]
    exact sub_eq_neg_self.mp hi
  have hd:=(jX _ _ _).mp hh
  simp only [sub_zero] at hd
  exact QD _ hd
namespace aD
variable {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} {δ:Type oG} [Fintype Ω]
lemma jB (p:aD Ω) (X:Ω → α) (Y:Ω → β) (C:Ω → γ) (D:Ω → δ)
    (hX:∀ ω ν,X ω=X ν ↔ Y ω=Y ν) (hC:∀ ω ν,C ω=C ν ↔ D ω=D ν) :
    p.bT X C=p.bT Y D:=by
  unfold bT
  rw [p.aZ C D hC]
  congr 1
  apply p.aZ
  intro ω ν
  simp only [Prod.mk.injEq,hX,hC]
end aD
lemma oz {ι:Type c9} (f:ι → GaussianInt) (x y:GaussianInt) :
    (fun i=>aR (f i) x)=(fun i=>aR (f i) y) ↔
      (fun i=>aY (f i) x)=(fun i=>aY (f i) y):=by
  simp only [funext_iff,k9,jX]
theorem DY {Ω:Type bU} {ι:Type c9} [Fintype Ω] [Fintype ι]
    (p:aD Ω) (t:Ω → ℕ) (z:ℕ → GaussianInt) {D:ℝ}
    (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f:ι → GaussianInt) (hf:∀ i,f i≠0) (L N a:ℕ) (ha:a≤N) :
    let P:=p.joint (fun _=>aD.uniform (Fin (N+1)))
    P.bT (fun v=>cw z L (t v.1+v.2.val+a))
      (fun v i=>aR (f i) (z (t v.1+v.2.val+a))) ≤
    P.bT (fun v=>cw z L (t v.1+v.2.val))
      (fun v i=>aR (f i) (z (t v.1+v.2.val)))+
      2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (bY D).card+
        2*∑ i,Real.log (f i).norm.natAbs):=by
  let (i:ι):Finite (GaussianInt ⧸ multiples (f i)):=kN (hf i)
  let (i:ι):Fintype (GaussianInt ⧸ multiples (f i)):=Fintype.ofFinite _
  dsimp only
  let P:=p.joint (fun _=>aD.uniform (Fin (N+1)))
  have he (u:Ω × Fin (N+1) → ℕ) :
      P.bT (fun v=>cw z L (u v)) (fun v i=>aR (f i) (z (u v))) =
      P.g7 (fun v=>kO z hz L (u v)) (fun v i=>aY (f i) (z (u v))):=by
    rw [show P.g7 (fun v=>kO z hz L (u v))
      (fun v i=>aY (f i) (z (u v))) =
      P.bT (fun v=>kO z hz L (u v))
      (fun v i=>aY (f i) (z (u v))) by
        simp only [aD.g7,aD.bT,aD.jW]]
    apply P.jB
    · intro v w; exact (oR z hz L (u v) (u w)).symm
    · intro v w; exact oz f _ _
  have h:=p.N5 t N a ha (kO z hz L)
    (fun t i=>aY (f i) (z t))
  have hc:Real.log (Fintype.card ((i:ι) → GaussianInt ⧸ multiples (f i))) =
      ∑ i,Real.log (f i).norm.natAbs:=by
    rw [Fintype.card_pi,Nat.cast_prod,Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [← Nat.card_eq_fintype_card,l5 (hf i)]
    · intro i _
      exact_mod_cast Fintype.card_ne_zero
  change P.bT _ _ ≤ P.bT _ _+_+_
  rw [he,he]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,
    Real.log_pow,hc] using h
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9 bU cD jY Rg gQ
namespace GaussianMoat
open scoped BigOperators Classical
abbrev aE.bZ (s:aE):=(Fin s.primes.card → Bool) × Fin s.primes.card
noncomputable def aE.bD (s:aE) (i:s.bZ):ℕ :=
  s.enumeration i.2
noncomputable def aE.fO (s:aE) (i:s.bZ):GaussianInt :=
  dG (s.factor (s.bD i)) (i.1 i.2)
lemma aE.n7 (s:aE) (i:s.bZ) :
    (s.fO i).norm = (s.bD i:ℤ):=by
  rw [fO,iW]
  exact s.jc _ (s.enumeration i.2).property
lemma aE.qH (s:aE) (i:s.bZ) :
    s.fO i≠0:=by
  intro h
  have hn:=s.n7 i
  rw [h] at hn
  have hp:=(s.iF _ (s.enumeration i.2).property).ne_zero
  apply hp
  change s.bD i = 0
  simpa only [Zsqrtd.norm_zero,Nat.cast_eq_zero] using hn.symm
abbrev aE.Residue (s:aE) (i:s.bZ) :=
  GaussianInt ⧸ multiples (s.fO i)
noncomputable instance aE.Vd (s:aE) (i:s.bZ) :
    Fintype (s.Residue i):=by
  let:=kN (s.qH i)
  exact Fintype.ofFinite _
lemma aE.lH (s:aE) (i:s.bZ) :
    Fintype.card (s.Residue i)=s.bD i:=by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (GaussianInt ⧸ multiples (s.fO i)) = _
  rw [l5 (s.qH i),s.n7]
  simp
noncomputable def aE.residue (s:aE) (i:s.bZ) :
    GaussianInt → s.Residue i:=aY (s.fO i)
lemma aE.E3 (s:aE) (i:s.bZ) (z w:GaussianInt) :
    s.residue i z=s.residue i w ↔ s.bC i.1 z i.2=s.bC i.1 w i.2:=by
  change aY _ z=aY _ w ↔ aR _ z=aR _ w
  rw [jX,k9]
  rfl
lemma aD.OL {ι:Type c9} [Fintype ι] [Nonempty ι] (f:ι → ℝ) :
    (∑ i,aD.uniform ι i*f i)=𝔼 i,f i:=by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [aD.m4,← Finset.mul_sum,div_eq_inv_mul]
lemma aE.dY (s:aE) (hne:s.primes.Nonempty) :
    Nonempty s.bZ:=by
  have hk:=hne.card_pos
  exact ⟨(fun _=>true,⟨0,hk⟩)⟩
theorem aE.pO {Ω:Type bU} {α:Type cD} [Fintype Ω]
    (s:aE) (hne:s.primes.Nonempty) (p:aD Ω)
    (Z:Ω → GaussianInt) (C:Ω → α) (a:GaussianInt) {b:ℕ}
    (hb:0<b) (hbk:b ≤ s.primes.card) {e E:ℝ}
    (hH:(1-e)*(b:ℝ)*s.aP ≤ s.aV p Z b)
    (hC:p.Hf C≤E) :
    letI:=s.dY hne
    (∑ i:s.bZ,aD.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      p.bT (fun ω=>s.residue i (Z ω-a)) C)) ≤ e*s.aP+E/b:=by
  let:=s.dY hne
  have hc:=s.EZ p Z C hbk
  have he (i:s.bZ) :
      p.bT (fun ω=>s.residue i (Z ω-a)) C =
        p.bT (fun ω=>s.bC i.1 (Z ω) i.2) C:=by
    apply p.jB _ _ _ _
    · intro ω ν
      change aY _ (Z ω-a)=aY _ (Z ν-a) ↔ _
      rw [lP,lP,sub_left_inj]
      exact s.E3 i _ _
    · intro ω ν; rfl
  have hd:(∑ i:s.bZ,aD.uniform _ i*
      (Real.log (Fintype.card (s.Residue i))-p.bT (fun ω=>s.residue i (Z ω-a)) C)) =
      s.aP-(𝔼 σ:Fin s.primes.card → Bool,𝔼 i:Fin s.primes.card,
        p.bT (fun ω=>s.bC σ (Z ω) i) C):=by
    rw [aD.OL]
    simp only [s.lH,he,Finset.expect_sub_distrib]
    simp only [← Finset.univ_product_univ,Finset.expect_product]
    simp only [bD,aP,Fintype.expect_const]
  rw [hd]
  have hbp:(0:ℝ)<b:=by exact_mod_cast hb
  apply (mul_le_mul_iff_left₀ hbp).mp
  have hgoal:(s.aP-(𝔼 σ:Fin s.primes.card → Bool,𝔼 i:Fin s.primes.card,
      p.bT (fun ω=>s.bC σ (Z ω) i) C))*(b:ℝ) ≤
        (e*s.aP+E/b)*(b:ℝ):=by
    rw [add_mul,div_mul_cancel₀ _ hbp.ne']
    nlinarith only [hc,hH,hC]
  exact hgoal
namespace aD
variable {G:Type jY} [Fintype G]
noncomputable def cW (p:aD G) (τ:ℝ):Finset G :=
  Finset.univ.filter (fun x=>p x<τ/(Fintype.card G:ℝ))
lemma tZ (p:aD G) (τ:ℝ) (x:G) :
    x∉p.cW τ ↔ τ/(Fintype.card G:ℝ)≤p x:=by
  simp only [cW,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]
lemma MQ (p:aD G) (τ:ℝ) :
    p.prob (fun x=>x∈p.cW τ) ≤ τ*(p.cW τ).card/(Fintype.card G:ℝ):=by
  have he:p.prob (fun x=>x∈p.cW τ)=∑ x∈p.cW τ,p x:=by
    unfold prob
    trans ∑ x,if x∈p.cW τ then p.mass x else 0
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [he]
  have hh:=Finset.sum_le_sum (s:=p.cW τ) (fun x hx =>
    ((Finset.mem_filter.mp hx).2).le)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have heq:((p.cW τ).card:ℝ)*(τ/(Fintype.card G:ℝ)) =
      τ*(p.cW τ).card/(Fintype.card G:ℝ):=by ring
  rw [heq] at hh
  exact hh
lemma Tw {G':Type Rg} [Fintype G'] (p:aD G) (e:G ≃ G') (τ:ℝ) :
    ((p.map e).cW τ).card=(p.cW τ).card:=by
  have h:(p.map e).cW τ=(p.cW τ).image e:=by
    ext x
    simp only [cW,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_image,lA,Fintype.card_congr e]
    constructor
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      simpa only [e.symm_apply_apply] using hy
  rw [h,Finset.card_image_of_injective _ e.injective]
theorem MW {ι:Type c9} [Fintype ι]
    (G:ι → Type jY) [∀ i,Fintype (G i)] (w:aD ι)
    (p:(i:ι) → aD (G i)) (u:ι → ℝ) {τ b e:ℝ}
    (hτ:τ≤3/8) (hb:0<b)
    (hu:∀ i,8*b*(Fintype.card (G i):ℝ) ≤ u i)
    (hdef:(∑ i,w i*(Real.log (Fintype.card (G i))-(p i).entropy))≤e) :
    w.prob (fun i=>u i≤((p i).cW τ).card) ≤ e/b:=by
  apply ML G w p (fun i=>(p i).cW τ) _ hb
  · intro i x hx
    exact ((Finset.mem_filter.mp hx).2).le.trans
      (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _))
  · intro i hi
    have hne:=(p i).nonempty
    have hp:(0:ℝ)<Fintype.card (G i):=by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ (by positivity:(0:ℝ)<8*(Fintype.card (G i):ℝ))).mpr
    nlinarith only [hu i,hi]
  · exact hdef
theorem GO {Ω:Type bU} {Γ:Type gQ} {ι:Type c9} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G:ι → Type jY) [∀ i,Fintype (G i)] [∀ i,AddCommGroup (G i)]
    (w:aD ι) (p:aD Ω) (q:Ω → aD Γ)
    (Y:(i:ι) → Ω → G i) (h:(i:ι) → Γ → G i)
    (u u' b:ι → ℝ) {τ δ ε η η' e v:ℝ} {n:ℕ}
    (hn:0<n) (hτ:0≤τ) (hτ1:τ≤3/8) (hδ:0<δ) (hδ1:δ≤1/64)
    (hε:0≤ε) (hη:0<η) (hu:∀ i,0<u i)
    (hnext:∑ i,w i*p.prob (fun ω=>u' i≤
      (((q ω).map (h i)).cW (τ+4*δ)).card) ≤ η')
    (jd:η'+ε≤η*δ/2) (jR:2*(1-Real.log (η*δ/2))≤v)
    (jI:e<η*δ*v/4)
    (kC:(∑ i,w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω=>(q ω).f6 n)).bT (fun x=>Y i x.1) Prod.snd))≤e)
    (hb:∀ i,1≤b i)
    (hv:∀ i,v≤Real.log (Fintype.card (G i))-Real.log (b i))
    (hu':∀ i,u' i/δ≤b i)
    (iJ:∀ i,(Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*u i/(2*(Fintype.card (G i):ℝ)))≤ε) :
    w.prob (fun i=>u i≤(((p.joint q).map (fun x=>Y i x.1+h i x.2)).cW τ).card) ≤ η:=by
  let P:=fun i=>(p.joint q).map (fun x=>Y i x.1+h i x.2)
  let K:=fun i=>(P i).cW τ
  let B₀:=fun i=>u i≤(K i).card
  let B₁:=fun i ω=>u' i≤(((q ω).map (h i)).cW (τ+4*δ)).card
  let E:=fun i ω=>(((q ω).map (h i)).cW (τ+4*δ))
  apply DN G w p q Y h B₀ B₁ K E b hn hτ hτ1 hδ hδ1
    hε hη hnext jd jR jI kC
  · intro i hi
    apply Finset.card_pos.mp
    have hh:(0:ℝ)<(K i).card:=(hu i).trans_le hi
    exact_mod_cast hh
  · intro i _; exact hb i
  · intro i _; exact hv i
  · intro i _
    have hh:=(P i).MQ τ
    rw [oN] at hh
    exact hh
  · intro i _ ω _ x hx
    exact (((q ω).map (h i)).tZ _ x).mp hx
  · intro i _ ω hω
    have hh:((E i ω).card:ℝ)<u' i:=lt_of_not_ge hω
    exact (div_le_div_of_nonneg_right hh.le hδ.le).trans (hu' i)
  · intro i hi
    apply le_trans _ (iJ i)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_left hi (show 0≤(n:ℝ)*δ^2 by positivity)
    have hd:=div_le_div_of_nonneg_right hh
      (show 0≤2*(Fintype.card (G i):ℝ) by positivity)
    simpa only [neg_mul,neg_div] using neg_le_neg hd
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
universe cD bU dD
namespace GaussianMoat
open scoped BigOperators Classical
noncomputable def aO.l8 (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a:ℕ) :
    Fin (K.bound+1) → bY (D*K.bound):=fun i =>
  ⟨z (a+i.val)-z a,(lZ _ _).mpr (by
    simpa only [Nat.add_zero] using g8 z hD hs a K.bound i.val 0
      (by omega) (by omega))⟩
noncomputable def aO.gX (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a:ℕ) :
    aD (bY (D*K.bound)) :=
  (K.law a).map (K.l8 z hD hs a)
lemma aO.QW (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a:ℕ)
    {α:Type cD} [Fintype α] (f:GaussianInt → α) :
    (K.gX z hD hs a).map (fun d=>f (d.val+z a))=
      (K.law a).map (fun i=>f (z (a+i.val))):=by
  rw [gX,aD.map_comp]
  congr 1
  funext i
  simp only [Function.comp_def,l8,sub_add_cancel]
theorem zH {Ω:Type bU} [Fintype Ω] (p:aD Ω)
    (a:Ω → ℕ) (K:aO) (z:ℕ → GaussianInt) {D:ℝ}
    (hD:1≤D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (hK:1≤K.bound) (n:ℕ) :
    (p.joint (fun ω=>(K.gX z (by linarith only [hD]) hs (a ω)).f6 n)).Hf
      Prod.snd ≤ n*(Real.log 36+2*Real.log (D*K.bound)):=by
  let q:=fun ω=>(K.gX z (by linarith only [hD]) hs (a ω)).f6 n
  have hh:=(p.joint q).kF Prod.snd
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] at hh
  have hR:1≤D*K.bound:=one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  have hc:(0:ℝ)<(bY (D*K.bound)).card:=by
    exact_mod_cast Finset.card_pos.mpr ⟨0,by simpa using (show 0≤D*K.bound by positivity)⟩
  have hl:=Real.log_le_log hc (tW hR)
  rw [Real.log_mul (by norm_num:(36:ℝ)≠0)
    (pow_ne_zero _ (by linarith only [hR]:D*K.bound≠0)),Real.log_pow] at hl
  exact hh.trans (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))
lemma Qk {Ω:Type bU} [Fintype Ω] (s:aE)
    (p:aD Ω) (a:Ω → ℕ) (K:aO) (z:ℕ → GaussianInt) {D:ℝ}
    (hD:0≤D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (n b:ℕ) :
    s.aV (p.joint (fun ω=>(K.gX z hD hs (a ω)).f6 n))
      (fun v=>z (a v.1)) b = s.aV p (fun ω=>z (a ω)) b:=by
  let q:Ω → aD (Fin n → bY (D*K.bound)):=fun ω =>
    (K.gX z hD hs (a ω)).f6 n
  exact s.jQ p q (fun ω=>z (a ω)) b
noncomputable def aO.cV (K:aO)
    (s:aE) (z:ℕ → GaussianInt) (a:ℕ) (i:s.bZ):aD (s.Residue i) :=
  (K.law a).map (fun t=>s.residue i (z (a+t.val)-z a))
lemma aO.Ci (K:aO)
    (s:aE) (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a:ℕ) (i:s.bZ) :
    (K.gX z hD hs a).map (fun d=>s.residue i d.val)=
      K.cV s z a i:=by
  rw [aO.gX,aD.map_comp]
  rfl
lemma aO.Cj (K R:aO)
    (s:aE) (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a:ℕ) (i:s.bZ) :
    (K.then R).cV s z a i =
      ((K.law a).joint (fun t=>R.gX z hD hs (a+t.val))).map
        (fun v=>s.residue i (z (a+v.1.val)-z a)+s.residue i v.2.val):=by
  unfold cV aO.then
  rw [aD.map_comp,aD.gW,aD.gW]
  congr 1
  funext t
  rw [aO.gX,aD.map_comp]
  congr 1
  funext u
  change s.residue i (z (a+(t.val+u.val))-z a) =
    s.residue i (z (a+t.val)-z a)+s.residue i (z (a+t.val+u.val)-z (a+t.val))
  unfold aE.residue
  rw [← Jp]
  congr 1
  rw [Nat.add_assoc]
  abel
lemma aD.N7 {Ω:Type bU} {α:Type cD} {β:Type dD} [Fintype Ω]
    (p:aD Ω) (X:Ω → α) (c:β):p.bT X (fun _=>c)=p.Hf X:=by
  unfold bT
  rw [p.Ao,sub_zero]
  apply p.aZ
  intro ω ν
  simp only [Prod.mk.injEq,and_true]
lemma aO.N8 (K:aO)
    (s:aE) (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) (a:ℕ)
    {b:ℕ} (hb:0<b) (hbk:b≤ s.primes.card) {e:ℝ}
    (hH:(1-e)*(b:ℝ)*s.aP≤ s.aV (K.law a) (fun t=>z (a+t.val)) b) :
    letI:=s.dY hne
    (∑ i:s.bZ,aD.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      (K.cV s z a i).entropy))≤e*s.aP:=by
  let:=s.dY hne
  have hh:=s.pO hne (K.law a) (fun t=>z (a+t.val))
    (fun _=>()) (z a) hb hbk hH (E:=0) (by rw [aD.Ao])
  simp only [aD.N7,zero_div,add_zero] at hh
  change (∑ i,aD.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
    (K.law a).H (fun t=>s.residue i (z (a+t.val)-z a))))≤_
  simpa only [aD.jW] using hh
theorem aO.PW (K:aO)
    (s:aE) (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) (a:ℕ)
    {b:ℕ} (hb:0<b) (hbk:b≤ s.primes.card) {e τ c:ℝ} (u:s.bZ → ℝ)
    (hτ:τ≤3/8) (hc:0<c) (hu:∀ i,8*c*(s.bD i:ℝ)≤u i)
    (hH:(1-e)*(b:ℝ)*s.aP≤ s.aV (K.law a) (fun t=>z (a+t.val)) b) :
    letI:=s.dY hne
    (aD.uniform s.bZ).prob (fun i =>
      u i≤((K.cV s z a i).cW τ).card) ≤e*s.aP/c:=by
  let:=s.dY hne
  apply aD.MW s.Residue (aD.uniform _) (K.cV s z a) u
    hτ hc
  · intro i
    simpa only [s.lH] using hu i
  · exact K.N8 s hne z a hb hbk hH
lemma aO.E4 (K R:aO)
    (s:aE) (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) {D:ℝ}
    (hD:1≤D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (hR:1≤R.bound)
    (a n:ℕ) {b:ℕ} (hb:0<b) (hbk:b≤ s.primes.card) {e:ℝ}
    (hH:(1-e)*(b:ℝ)*s.aP≤ s.aV (K.law a) (fun t=>z (a+t.val)) b) :
    letI:=s.dY hne
    (∑ i:s.bZ,aD.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      ((K.law a).joint (fun t=>(R.gX z (by linarith only [hD]) hs (a+t.val)).f6 n)).bT
        (fun v=>s.residue i (z (a+v.1.val)-z a)) Prod.snd)) ≤
      e*s.aP+n*(Real.log 36+2*Real.log (D*R.bound))/b:=by
  let:=s.dY hne
  let q:=fun t:Fin (K.bound+1) =>
    (R.gX z (by linarith only [hD]) hs (a+t.val)).f6 n
  let P:=(K.law a).joint q
  have he:s.aV P (fun v=>z (a+v.1.val)) b =
      s.aV (K.law a) (fun t=>z (a+t.val)) b :=
    s.jQ (K.law a) q (fun t=>z (a+t.val)) b
  have hH':(1-e)*(b:ℝ)*s.aP≤ s.aV P (fun v=>z (a+v.1.val)) b:=by
    rw [he]; exact hH
  exact s.pO hne P (fun v=>z (a+v.1.val)) Prod.snd (z a)
    hb hbk hH' (zH (K.law a) (fun t=>a+t.val) R z hD hs hR n)
theorem aO.Lq (K R:aO)
    (s:aE) (hne:s.primes.Nonempty) (z:ℕ → GaussianInt) {D:ℝ}
    (hD:1≤D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (hR:1≤R.bound)
    (a:ℕ) (u u' c:s.bZ → ℝ) {τ δ ε η η' e v:ℝ} {n b:ℕ}
    (hn:0<n) (hb:0<b) (hbk:b≤ s.primes.card)
    (hτ:0≤τ) (hτ1:τ≤3/8) (hδ:0<δ) (hδ1:δ≤1/64)
    (hε:0≤ε) (hη:0<η) (hu:∀ i,0<u i)
    (hH:(1-e)*(b:ℝ)*s.aP≤ s.aV (K.law a) (fun t=>z (a+t.val)) b)
    (hnext:∀ t,letI:=s.dY hne
      (aD.uniform s.bZ).prob (fun i=>u' i≤
        ((R.cV s z t i).cW (τ+4*δ)).card)≤η')
    (jd:η'+ε≤η*δ/2) (jR:2*(1-Real.log (η*δ/2))≤v)
    (jI:e*s.aP+n*(Real.log 36+2*Real.log (D*R.bound))/b<η*δ*v/4)
    (hc:∀ i,1≤c i) (hv:∀ i,v≤Real.log (s.bD i)-Real.log (c i))
    (hu':∀ i,u' i/δ≤c i)
    (iJ:∀ i,(s.bD i:ℝ)*Real.exp
      (-(n:ℝ)*δ^2*u i/(2*(s.bD i:ℝ)))≤ε) :
    letI:=s.dY hne
    (aD.uniform s.bZ).prob (fun i =>
      u i≤(((K.then R).cV s z a i).cW τ).card)≤η:=by
  let:=s.dY hne
  let w:=aD.uniform s.bZ
  let q:=fun t:Fin (K.bound+1)=>R.gX z (by linarith only [hD]) hs (a+t.val)
  have Yf:(∑ i,w i*(K.law a).prob (fun t=>u' i≤
      (((q t).map (fun d=>s.residue i d.val)).cW (τ+4*δ)).card))≤η':=by
    simp only [q,aO.Ci,aD.prob,Finset.mul_sum]
    rw [Finset.sum_comm]
    have he:(∑ t,∑ i,w i*(if u' i≤
        ((R.cV s z (a+t.val) i).cW (τ+4*δ)).card then K.law a t else 0)) =
        ∑ t,K.law a t*w.prob (fun i=>u' i≤
          ((R.cV s z (a+t.val) i).cW (τ+4*δ)).card):=by
      unfold aD.prob
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [he]
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun t _ =>
      mul_le_mul_of_nonneg_left (hnext (a+t.val)) ((K.law a).nonneg t))
    simpa only [← Finset.sum_mul,(K.law a).dN,one_mul] using hh
  have hd:=K.E4 R s hne z hD hs hR a n hb hbk hH
  have hh:=aD.GO s.Residue w (K.law a) q
    (fun i t=>s.residue i (z (a+t.val)-z a)) (fun i d=>s.residue i d.val)
    u u' c hn hτ hτ1 hδ hδ1 hε hη hu Yf jd jR jI hd hc
    (by intro i; simpa only [s.lH] using hv i) hu'
    (by intro i; simpa only [s.lH] using iJ i)
  have he (i:s.bZ):=K.Cj R s z
    (by linarith only [hD]) hs a i
  simpa only [he] using hh
structure fq (s:aE) (D:ℝ) (ns:List ℕ) (N b:ℕ) (δ:ℝ) where
  pre:List ℕ
  post:List ℕ
  g:ℝ
  U:ℝ
  l:ℕ
  e:ℝ
  schedule:ns=pre++List.ofFn (fun i:Fin l=>f9 g U i.val)++post
  size:b=eD s g U l
  positive:0<g
  small:g≤1/200
  scale:0<U
  logarithmic:2*(1+Real.log 18)≤g*aW g U l
  large:640*s.aP≤g^5*aW g U l
  alphabet:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ))≤g^2*aW g U l
  displacement:4*Real.log D+2*Real.log 36≤4*g*aW g U l
  geometry:2*Real.log 16+4*Real.log D≤aW g U l/4
  cap:⌊U/s.aP⌋₊≤ s.primes.card
  cost:Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤e*(eD s g U l:ℝ)*s.aP
  Yw:(1/2:ℝ)^l+80*g+e≤δ
theorem fq.sound {s:aE} {D T:ℝ} {ns:List ℕ} {N b:ℕ} {δ:ℝ}
    (q:fq s D ns N b δ) (hne:s.primes.Nonempty)
    (z:ℕ → GaussianInt) (hz:Function.Injective z) (hD:1≤D) (hT:5≤T)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T) (hL:1≤ s.aP) (a:ℕ) :
    (1-δ)*(b:ℝ)*s.aP≤
      s.aV ((b9 z ns N).law a) (fun t=>z (a+t.val)) b:=by
  rcases q with ⟨pre,post,g,U,l,e,heq,hb,hg,hg1,hU,hlog,cQ,hsize,sw,sI,hcap,jz,hδ⟩
  subst ns b
  have hh:=sK s hne z hz pre post a N hD hT hs hpT
    hg hg1 hL hU hlog cQ hsize sw sI hcap jz
  have hn:0≤(eD s g U l:ℝ)*s.aP:=mul_nonneg (Nat.cast_nonneg _) (by linarith only [hL])
  nlinarith only [hh,hδ,hn]
inductive gG (s:aE) (D:ℝ) (N:ℕ) :
    List ℕ → ℝ → (s.bZ → ℝ) → ℝ → Prop
  | base (ns:List ℕ) (b:ℕ) (τ c e η:ℝ) (u:s.bZ → ℝ)
      (DZ:fq s D ns N b e)
      (hb:0<b) (hbk:b≤ s.primes.card) (hτ:τ≤3/8) (hc:0<c)
      (hu:∀ i,8*c*(s.bD i:ℝ)≤u i) (hη:e*s.aP/c≤η) :
      gG s D N ns τ u η
  | step (ns rest:List ℕ) (b n:ℕ) (τ δ ε η η' e v:ℝ)
      (u u' c:s.bZ → ℝ)
      (DZ:fq s D ns 0 b e)
      (next:gG s D N rest (τ+4*δ) u' η')
      (hR:1≤rest.sum+N) (hn:0<n) (hb:0<b) (hbk:b≤ s.primes.card)
      (hτ:0≤τ) (hτ1:τ≤3/8) (hδ:0<δ) (hδ1:δ≤1/64)
      (hε:0≤ε) (hη:0<η) (hu:∀ i,0<u i)
      (jd:η'+ε≤η*δ/2) (jR:2*(1-Real.log (η*δ/2))≤v)
      (jI:e*s.aP+n*(Real.log 36+2*Real.log (D*(rest.sum+N)))/b<η*δ*v/4)
      (hc:∀ i,1≤c i) (hv:∀ i,v≤Real.log (s.bD i)-Real.log (c i))
      (hu':∀ i,u' i/δ≤c i)
      (iJ:∀ i,(s.bD i:ℝ)*Real.exp
        (-(n:ℝ)*δ^2*u i/(2*(s.bD i:ℝ)))≤ε) :
      gG s D N (ns++rest) τ u η
theorem gG.sound {s:aE} {D T:ℝ} {N:ℕ}
    {ns:List ℕ} {τ η:ℝ} {u:s.bZ → ℝ}
    (q:gG s D N ns τ u η) (hne:s.primes.Nonempty)
    (z:ℕ → GaussianInt) (hz:Function.Injective z) (hD:1≤D) (hT:5≤T)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T) (hL:1≤ s.aP) :
    ∀ a,letI:=s.dY hne
      (aD.uniform s.bZ).prob (fun i=>u i≤
        (((b9 z ns N).cV s z a i).cW τ).card)≤η:=by
  let:=s.dY hne
  induction q with
  | base ns b τ c e η u DZ hb hbk hτ hc hu hη =>
    intro a
    exact ((b9 z ns N).PW s hne z a hb hbk u hτ hc hu
      (DZ.sound hne z hz hD hT hs hpT hL a)).trans hη
  | step ns rest b n τ δ ε η η' e v u u' c DZ next hR hn hb hbk hτ hτ1 hδ hδ1
      hε hη hu jd jR jI hc hv hu' iJ ih =>
    intro a
    rw [m8]
    apply (b9 z ns 0).Lq (b9 z rest N) s hne z
      hD hs (by simpa only [jG] using hR) a u u' c hn hb hbk hτ hτ1 hδ hδ1 hε hη hu
      (DZ.sound hne z hz hD hT hs hpT hL a) ih jd jR
    · simpa only [jG,Nat.cast_add] using jI
    · exact hc
    · exact hv
    · exact hu'
    · exact iJ
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU c9 jY cD zV gQ dD g4 oG
namespace GaussianMoat
namespace aD
open scoped BigOperators Classical
lemma OO {Ω:Type bU} {ι:Type c9} [Fintype Ω] [Fintype ι]
    (G:ι → Type jY) (p:aD Ω) (X:(i:ι) → Ω → G i) {α:Type cD} (C:Ω → α) :
    p.bT (fun ω i=>X i ω) C ≤ ∑ i,p.bT (X i) C:=by
  let Y:=fun ω i=>(⟨i,X i ω⟩:Σ i,G i)
  have he:p.bT (fun ω i=>X i ω) C = p.bT Y C:=by
    apply p.jB _ _ _ _
    · intro ω ν
      constructor
      · intro h; funext i; exact congrArg (Sigma.mk i) (congrFun h i)
      · intro h; funext i; exact Sigma.mk.inj_iff.mp (congrFun h i) |>.2 |> eq_of_heq
    · intro ω ν; rfl
  rw [he]
  apply (p.l6 Y C).trans
  apply Finset.sum_le_sum
  intro i _
  apply le_of_eq
  apply p.jB _ _ _ _
  · intro ω ν
    exact ⟨fun h=>eq_of_heq (Sigma.mk.inj_iff.mp h).2,fun h=>congrArg (Sigma.mk i) h⟩
  · intro ω ν; rfl
lemma E5 {ι:Type c9} {O:Type zV} {Γ:Type gQ} [Fintype ι] [Fintype O] [Fintype Γ]
    (G:ι → Type jY) [∀ i,Fintype (G i)]
    (p:aD (O × (∀ i,G i))) (q:O × (∀ i,G i) → aD Γ)
    (hit:(i:ι) → Γ → G i → Prop) (n:ℕ)
    (sP:∀ a,p a≠0 → ∀ v,q a v≠0 → ∀ i,¬ hit i v (a.2 i)) :
    (p.joint (fun a=>(q a).f6 n)).bT (fun v=>v.1.2)
      (fun v=>(v.1.1,v.2)) ≤
      ∑ a,p a*(∑ i,∑ v,(q a).f6 n v*Real.log (d9 (hit i) n v).card):=by
  let P:=p.joint (fun a=>(q a).f6 n)
  let C:=fun v:(O × (∀ i,G i)) × (Fin n → Γ)=>(v.1.1,v.2)
  have Rh (i:ι) :
      P.bT (fun v=>v.1.2 i) C ≤ ∑ v,P v*Real.log (d9 (hit i) n v.2).card:=by
    have hh:=P.wC (fun v=>v.1.2 i) C
      (fun c x=>∃ j,hit i (c.2 j) x) (by
        intro v hv
        have hm:p v.1≠0 ∧ (q v.1).f6 n v.2≠0:=mul_ne_zero_iff.mp hv
        have hx:=(q v.1).qU (hit i) (v.1.2 i)
          (fun a ha=>sP v.1 hm.1 a ha i) n v.2 hm.2
        simpa only [d9,Finset.mem_filter,Finset.mem_univ,true_and,not_exists] using hx)
    have hh':P.bT (fun v=>v.1.2 i) C ≤
        ∑ c,(P.map C) c * Real.log (d9 (hit i) n c.2).card:=by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro c _
      simp only [d9,not_exists]
    rw [N4] at hh'
    exact hh'
  have hs:=P.OO G (fun i v=>v.1.2 i) C
  apply hs.trans
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun i _=>Rh i)).trans
  apply le_of_eq
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,← mul_assoc]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [P,jv]
theorem zK {ι:Type c9} {O:Type zV} {Γ:Type gQ} [Fintype ι] [Fintype O] [Fintype Γ]
    (G:ι → Type jY) [∀ i,Fintype (G i)]
    (p:aD (O × (∀ i,G i))) (q:O × (∀ i,G i) → aD Γ)
    (hit:(i:ι) → Γ → G i → Prop) (n:ℕ)
    (sP:∀ a,p a≠0 → ∀ v,q a v≠0 → ∀ i,¬ hit i v (a.2 i))
    (Bad:ι → O × (∀ i,G i) → Prop) {A e η:ℝ} (hA:0≤A)
    (hH:(∑ i,Real.log (Fintype.card (G i)))-e ≤ p.bT Prod.snd Prod.fst)
    (Bm:(∑ i,p.prob (Bad i)) ≤ η)
    (hlist:∀ a,p a≠0 → ∀ i,
      (∑ v,(q a).f6 n v*Real.log (d9 (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1)) :
    A*((Fintype.card ι:ℝ)-η)-e ≤
      (n:ℝ)*(p.joint q).i7 (fun v=>v.1.2) Prod.snd (fun v=>v.1.1):=by
  let P:=p.joint (fun a=>(q a).f6 n)
  have hcond:=E5 G p q hit n sP
  have hsum:(∑ a,p a*(∑ i,∑ v,(q a).f6 n v*Real.log (d9 (hit i) n v).card)) ≤
      (∑ i,Real.log (Fintype.card (G i)))-A*((Fintype.card ι:ℝ)-∑ i,p.prob (Bad i)):=by
    calc
      _ ≤ ∑ a,p a*(∑ i,(Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1))):=by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha:p a=0
        · simp only [ha,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hlist a ha i)) (p.nonneg a)
      _ = _:=by
        simp only [Finset.sum_sub_distrib,mul_sub,
          ← Finset.sum_mul,p.dN,one_mul]
        congr 1
        rw [mul_comm]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        have hh (i:ι):(∑ a,p a*(if Bad i a then (0:ℝ) else 1))=1-p.prob (Bad i):=by
          rw [← p.pI]
          unfold prob
          apply Finset.sum_congr rfl
          intro a _
          by_cases hb:Bad i a <;> simp [hb]
        have hh' (i:ι):(∑ a,p a*(A*(if Bad i a then (0:ℝ) else 1)))=
            A*(1-p.prob (Bad i)):=by
          rw [← hh i,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        simp only [hh',mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,
          Finset.card_univ,nsmul_eq_mul]
  have W7:P.bT (fun v=>v.1.2) (fun v=>v.1.1)=p.bT Prod.snd Prod.fst:=by
    have hh:=P.vh Prod.fst Prod.snd Prod.fst
    rw [qM] at hh
    exact hh.symm
  have kT:A*((Fintype.card ι:ℝ)-η)-e ≤
      P.i7 (fun v=>v.1.2) Prod.snd (fun v=>v.1.1):=by
    unfold i7
    rw [W7]
    have hm:=mul_le_mul_of_nonneg_left Bm hA
    change P.bT (fun v=>v.1.2) (fun v=>(v.1.1,v.2)) ≤ _ at hcond
    linarith only [hH,hcond,hsum,hm]
  exact kT.trans (wB p q n)
open scoped BigOperators Classical
variable {Ω:Type bU} {α:Type cD} {Γ:Type gQ} [Fintype Ω] [Fintype α] [Fintype Γ]
lemma Jr (p:aD Ω) (C:Ω → α) (a:α)
    (ha:p.map C a≠0) (ω:Ω) (hω:p.eO C a ω≠0) :
    p ω≠0 ∧ C ω=a:=by
  have hh:=p.oM C a ω
  have hn:=mul_ne_zero ha hω
  rw [hh] at hn
  split_ifs at hn with hc
  · exact ⟨hn,hc⟩
  · exact False.elim (hn rfl)
lemma E9 (p:aD Ω) (C:Ω → α) (q:Ω → aD Γ) :
    (p.map C).joint (fun a=>(p.eO C a).mix q)=
      (p.joint q).map (fun v=>(C v.1,v.2)):=by
  apply aD.ext; rintro ⟨a,v⟩
  rw [jv,kV,Finset.mul_sum]
  conv_rhs=>rw [f7,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← mul_assoc,oM]
  simp only [jv,Prod.mk.injEq]
  by_cases hc:C ω=a
  · simp only [hc,true_and,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
  · simp only [hc,false_and,ite_false,zero_mul,Finset.sum_const_zero]
lemma Ri (p:aD Ω) (q:Ω → aD Γ) (v:Γ)
    (hv:p.mix q v≠0):∃ ω,p ω≠0 ∧ q ω v≠0:=by
  rw [kV] at hv
  obtain ⟨ω,_,hω⟩:=Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨ω,(mul_ne_zero_iff.mp hω)⟩
lemma qV {G:Type jY} [Fintype G]
    (q:aD Γ) (hit:Γ → G → Prop) (x:G)
    (sP:∀ v,q v≠0 → ¬hit v x) (n:ℕ) :
    (∑ v,q.f6 n v*Real.log (d9 hit n v).card) ≤ Real.log (Fintype.card G):=by
  have hh (v:Fin n → Γ):q.f6 n v*Real.log (d9 hit n v).card ≤
      q.f6 n v*Real.log (Fintype.card G):=by
    by_cases hv:q.f6 n v=0
    · simp only [hv,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ ((q.f6 n).nonneg v)
      apply Real.log_le_log
      · exact_mod_cast Finset.card_pos.mpr ⟨x,q.qU hit x sP n v hv⟩
      · exact_mod_cast Finset.card_le_univ (d9 hit n v)
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun v _=>hh v)
  simpa only [← Finset.sum_mul,(q.f6 n).dN,one_mul] using hs
lemma OP {β:Type dD} {γ:Type g4} {δ:Type oG} (p:aD Ω) (F:Ω → α)
    (X:α → β) (Y:α → γ) (Z:α → δ) :
    (p.map F).i7 X Y Z=p.i7 (X ∘ F) (Y ∘ F) (Z ∘ F):=by
  unfold i7
  rw [vh,vh]
  rfl
theorem pJ {ι:Type c9} {O:Type zV} [Fintype ι] [Fintype O]
    (G:ι → Type jY) [∀ i,Fintype (G i)]
    (p:aD Ω) (old:Ω → O) (X:Ω → ∀ i,G i) (q:Ω → aD Γ)
    (hit:(i:ι) → Γ → G i → Prop) (Good:ι → Ω → Prop)
    (E:(i:ι) → Ω → Finset (G i)) (e c:ι → ℝ) {A H η:ℝ} (n:ℕ)
    (hA:0≤A) (he:∀ i,0≤e i) (hc:∀ i,0≤c i)
    (sP:∀ ω,p ω≠0 → ∀ v,q ω v≠0 → ∀ i,¬hit i v (X ω i))
    (hE:∀ i ω,Good i ω → ((E i ω).card:ℝ)≤e i)
    (QC:∀ i ω,Good i ω → ∀ x∉E i ω,c i≤(q ω).prob (fun v=>hit i v x))
    (hH:(∑ i,Real.log (Fintype.card (G i)))-H ≤ p.bT X old)
    (Bm:(∑ i,p.prob (fun ω=>¬Good i ω))≤η)
    (hnum:∀ i,Real.log (4*e i+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4))) ≤
      Real.log (Fintype.card (G i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤
      (n:ℝ)*(p.joint q).i7 (fun v=>X v.1) Prod.snd (fun v=>old v.1):=by
  let C:=fun ω=>(old ω,X ω)
  let μ:=p.map C
  let Q:=fun a=>(p.eO C a).mix q
  let Bad:=fun i a=>(1/2:ℝ)<(p.eO C a).prob (fun ω=>¬Good i ω)
  have R6 (a:O × (∀ i,G i)) (ha:μ a≠0) (v:Γ) (hv:Q a v≠0) (i:ι) :
      ¬hit i v (a.2 i):=by
    obtain ⟨ω,hω,hv⟩:=(p.eO C a).Ri q v hv
    have hw:=p.Jr C a ha ω hω
    have hx:X ω=a.2:=congrArg Prod.snd hw.2
    rw [← hx]
    exact sP ω hw.1 v hv i
  have hH':(∑ i,Real.log (Fintype.card (G i)))-H ≤ μ.bT Prod.snd Prod.fst:=by
    rw [vh]
    exact hH
  have W8:(∑ i,μ.prob (Bad i))≤2*η:=by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      p.E0 C (fun ω=>¬Good i ω))
    simp only [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left Bm (by norm_num))
  have hlist (a:O × (∀ i,G i)) (ha:μ a≠0) (i:ι) :
      (∑ v,(Q a).f6 n v*Real.log (d9 (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1):=by
    by_cases hb:Bad i a
    · rw [dO hb,mul_zero,sub_zero]
      exact (Q a).qV (hit i) (a.2 i)
        (fun v hv=>R6 a ha v hv i) n
    · rw [gR hb,mul_one]
      have hg:(1/2:ℝ)≤(p.eO C a).prob (Good i):=by
        have hh:=(p.eO C a).pI (Good i)
        dsimp only [Bad] at hb
        push Not at hb
        linarith only [hh,hb]
      let F:=Finset.univ.filter (fun x:G i =>
        (p.eO C a).prob (fun ω=>Good i ω ∧ x∉E i ω)<1/4)
      have hf:(F.card:ℝ)≤4*e i :=
        (p.eO C a).Gv (Good i) (E i) (he i) (hE i) hg
      have hm (x:G i) (hx:x∉F):c i/4≤(Q a).prob (fun v=>hit i v x):=by
        apply (p.eO C a).Rd q (Good i) (E i) (hit i) (hc i) (QC i) x
        have hh:¬(p.eO C a).prob (fun ω=>Good i ω ∧ x∉E i ω)<1/4:=by
          simpa only [F,Finset.mem_filter,Finset.mem_univ,true_and] using hx
        exact le_of_not_gt hh
      have ht:=(Q a).tD (hit i) (a.2 i)
        (fun v hv=>R6 a ha v hv i) F hm n
      have hpos:(0:ℝ)<(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)):=by
        have hcard:0<Fintype.card (G i):=Fintype.card_pos_iff.mpr ⟨a.2 i⟩
        exact mul_pos (by exact_mod_cast hcard) (Real.exp_pos _)
      have hl:=Real.log_le_log (by positivity:(0:ℝ)<(F.card:ℝ)+
        (Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))
        (add_le_add hf (le_refl ((Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))))
      exact ht.trans (hl.trans (hnum i))
  have hh:=zK G μ Q hit n R6 Bad hA hH' W8 hlist
  have hdist:μ.joint Q=(p.joint q).map (fun v=>(C v.1,v.2)) :=
    p.E9 C q
  rw [hdist,OP] at hh
  exact hh
end aD
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU cD zV c9 Rj dD R7 g4 Rk gQ Kt qC
namespace GaussianMoat
open scoped BigOperators Classical
abbrev jS (D:ℝ) (B L:ℕ):=bY (D*B) × (Fin L → bY D)
noncomputable def aO.lV (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L:ℕ) (u:Fin (K.bound+1)) :
    jS D K.bound L :=
  (K.l8 z hD hs a u,kO z hs L (a+u.val))
noncomputable def aO.kq (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L:ℕ) :
    aD (jS D K.bound L) :=
  (K.law a).map (K.lV z hD hs a L)
noncomputable def jS.pfx {D:ℝ} {B L:ℕ}
    (v:jS D B L) (l:Fin L):GaussianInt :=
  v.1.val+∑ j:Fin l.val,(v.2 ⟨j.val,lt_trans j.isLt l.isLt⟩).val
lemma aO.sW (K:aO)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:0≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L:ℕ) (u:Fin (K.bound+1)) (l:Fin L) :
    (K.lV z hD hs a L u).pfx l=z (a+u.val+l.val)-z a:=by
  change z (a+u.val)-z a+(∑ j:Fin l.val,cw z l.val (a+u.val) j)=_
  rw [p9]
  abel
noncomputable def jS.QE {D:ℝ} {B L:ℕ}
    (π:GaussianInt) (v:jS D B L) (x:GaussianInt ⧸ multiples π):Prop :=
  ∃ l:Fin L,aY π (v.pfx l) = -x
lemma aO.Fd (K:aO)
    (π:GaussianInt) (z:ℕ → GaussianInt) (QD:∀ t,¬π∣z t)
    {D:ℝ} (hD:0≤D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (a L:ℕ) :
    ∀ v,K.kq z hD hs a L v≠0 → ¬jS.QE π v (aY π (z a)):=by
  intro v hv
  rw [kq,aD.f7] at hv
  obtain ⟨u,_,hu⟩:=Finset.exists_ne_zero_of_sum_ne_zero hv
  have he:K.lV z hD hs a L u=v:=by
    by_contra he
    simp only [gR he,ne_self_iff_false] at hu
  rw [← he]
  simpa only [jS.QE,K.sW] using Jq π z QD a (a+u.val) L
lemma aD.MY {Ω:Type bU} {α:Type cD} [Fintype Ω] [Fintype α]
    (p:aD Ω) (f:Ω → α) (x:α):p.map f x=p.prob (fun ω=>f ω=x):=rfl
theorem aO.D4 (R:aO)
    (π:GaussianInt) (z:ℕ → GaussianInt) (hz:Function.Injective z)
    {D τ:ℝ} (hD:0≤D) (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    {L N:ℕ} (j6:(D*L)^2<(π.norm:ℝ)) (LI:L≤N)
    (iJ:(L:ℝ)/(N+1)≤τ/2) (a:ℕ) (x:GaussianInt ⧸ multiples π)
    (hfloor:τ≤((R.then (dQ N)).law a).prob
      (fun u=>aY π (z (a+u.val)-z a) = -x)) :
    (L:ℝ)*τ/2≤((R.then (dQ N)).kq z hD hs a L).prob
      (fun v=>jS.QE π v x):=by
  have hf:τ≤((R.law a).joint (fun _=>aD.uniform (Fin (N+1)))).prob
      (fun v=>aY π (z (a+v.1.val+v.2.val)-z a) = -x):=by
    change τ≤(((R.law a).joint (fun _=>aD.uniform (Fin (N+1)))).map (ko R.bound N)).prob
      (fun (u:Fin (R.bound+N+1))=>aY π (z (a+u.val)-z a) = -x) at hfloor
    rw [aD.oN] at hfloor
    simpa only [ko,Nat.add_assoc] using hfloor
  have hh:=w8 (R.law a) π z hz hD hs j6 LI iJ a
    (fun u=>a+u.val) (-x) hf
  rw [kq,aD.oN]
  simp only [jS.QE,sW]
  change _≤(((R.law a).joint (fun _=>aD.uniform (Fin (N+1)))).map (ko R.bound N)).prob
    (fun (u:Fin (R.bound+N+1))=>∃ l:Fin L,aY π (z (a+u.val+l.val)-z a) = -x)
  rw [aD.oN]
  simpa only [ko,Nat.add_assoc] using hh
noncomputable def aO.qW (K:aO)
    (s:aE) (z:ℕ → GaussianInt) (a:ℕ) (i:s.bZ) (τ:ℝ) :
    Finset (s.Residue i):=((K.cV s z a i).cW τ).image Neg.neg
lemma aO.Fe (K:aO)
    (s:aE) (z:ℕ → GaussianInt) (a:ℕ) (i:s.bZ) (τ:ℝ) :
    (K.qW s z a i τ).card=((K.cV s z a i).cW τ).card:=by
  apply Finset.card_image_of_injective
  exact neg_injective
lemma aO.Bn (K:aO)
    (s:aE) (z:ℕ → GaussianInt) (a:ℕ) (i:s.bZ) (τ:ℝ) (x:s.Residue i)
    (hx:x∉K.qW s z a i τ) :
    τ/(s.bD i:ℝ)≤(K.cV s z a i) (-x):=by
  have hh : -x∉(K.cV s z a i).cW τ:=by
    intro h
    exact hx (Finset.mem_image.mpr ⟨-x,h,neg_neg x⟩)
  have he:=(K.cV s z a i).tZ τ (-x) |>.mp hh
  simpa only [s.lH] using he
lemma aE.P7 (s:aE) (z:GaussianInt)
    (h:z∈s.avoiding) (i:s.bZ):¬s.fO i∣z:=by
  have hh:=h (s.bD i) (s.enumeration i.2).property
  rcases i with ⟨σ,i⟩
  change ¬dG _ (σ i)∣z
  cases he:σ i <;> simp only [dG] <;> tauto
theorem qd {Ω:Type bU} {O:Type zV} {ι:Type c9}
    [Fintype Ω] [Fintype O] [Fintype ι]
    (s:aE) (p:aD Ω) (a:Ω → ℕ) (old:Ω → O)
    (I:ι → s.bZ) (R:aO)
    (z:ℕ → GaussianInt) (hz:Function.Injective z)
    (ha:∀ t,z t∈s.avoiding) {D τ A H η:ℝ} {L N n:ℕ}
    (hD:0≤D) (hτ:0≤τ) (hA:0≤A)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e:ι → ℝ) (he:∀ i,0≤e i)
    (j6:∀ i,(D*L)^2<(s.bD (I i):ℝ)) (LI:L≤N)
    (iJ:∀ i,(L:ℝ)/(N+1)≤(τ/(s.bD (I i):ℝ))/2)
    (hH:(∑ i,Real.log (s.bD (I i)))-H ≤
      p.bT (fun ω i=>s.residue (I i) (z (a ω))) old)
    (Bm:(∑ i,p.prob (fun ω=>e i≤
      (((R.then (dQ N)).cV s z (a ω) (I i)).cW τ).card))≤η)
    (hnum:∀ i,Real.log (4*e i+(s.bD (I i):ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.bD (I i):ℝ))/2)/4))) ≤
        Real.log (s.bD (I i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤ (n:ℝ)*
      (p.joint (fun ω=>(R.then (dQ N)).kq z hD hs (a ω) L)).i7
        (fun v i=>s.residue (I i) (z (a v.1))) Prod.snd (fun v=>old v.1):=by
  let K:=R.then (dQ N)
  let q:=fun ω=>K.kq z hD hs (a ω) L
  let Good:=fun i ω =>
    (((K.cV s z (a ω) (I i)).cW τ).card:ℝ)<e i
  apply aD.pJ (fun i=>s.Residue (I i)) p old
    (fun ω i=>s.residue (I i) (z (a ω))) q (fun i=>jS.QE (s.fO (I i)))
    Good (fun i ω=>K.qW s z (a ω) (I i) τ) e
    (fun i=>(L:ℝ)*(τ/(s.bD (I i):ℝ))/2) n hA he
  · intro i
    positivity
  · intro ω _ v hv i
    exact K.Fd (s.fO (I i)) z
      (fun t=>s.P7 (z t) (ha t) (I i)) hD hs (a ω) L v hv
  · intro i ω hg
    rw [aO.Fe]
    exact hg.le
  · intro i ω _ x hx
    apply R.D4 (s.fO (I i)) z hz hD hs
      (by simpa only [s.n7,Int.cast_natCast] using j6 i) LI (iJ i) (a ω) x
    have hh:=K.Bn s z (a ω) (I i) τ x hx
    simpa only [aO.cV,aD.MY,aE.residue] using hh
  · simpa only [s.lH] using hH
  · simpa only [Good,not_lt] using Bm
  · simpa only [s.lH] using hnum
namespace aD
lemma Bp {Ω:Type bU} {α:Type cD} {α':Type Rj} {β:Type dD} {β':Type R7} {γ:Type g4} {γ':Type Rk} [Fintype Ω]
    (p:aD Ω) (X:Ω → α) (X':Ω → α')
    (Y:Ω → β) (Y':Ω → β') (O:Ω → γ) (O':Ω → γ')
    (hX:∀ ω ν,X ω=X ν ↔ X' ω=X' ν)
    (hY:∀ ω ν,Y ω=Y ν ↔ Y' ω=Y' ν)
    (hO:∀ ω ν,O ω=O ν ↔ O' ω=O' ν) :
    p.i7 X Y O=p.i7 X' Y' O':=by
  unfold i7
  rw [p.jB X X' O O' hX hO]
  congr 1
  apply p.jB _ _ _ _ hX
  intro ω ν
  simp only [Prod.mk.injEq,hO,hY]
lemma P8 {Ω:Type bU} {Γ:Type gQ} {Γ':Type Kt} {α:Type cD} {β:Type dD} [Fintype Ω] [Fintype Γ] [Fintype Γ']
    (p:aD Ω) (q:Ω → aD Γ) (f:Ω → Γ → Γ') (X:Ω → α) (O:Ω → β) :
    (p.joint (fun ω=>(q ω).map (f ω))).i7 (fun v=>X v.1) Prod.snd (fun v=>O v.1)=
      (p.joint q).i7 (fun v=>X v.1) (fun v=>f v.1 v.2) (fun v=>O v.1):=by
  rw [← ow,OP]
  rfl
end aD
theorem aO.tJ {Ω:Type bU} {ι:Type c9} {κ:Type qC} [Fintype Ω]
    (K:aO) (p:aD Ω) (a:Ω → ℕ) (f:ι → GaussianInt) (g:κ → GaussianInt)
    (z:ℕ → GaussianInt) {D:ℝ} (hD:1≤D)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (hK:1≤K.bound) (L:ℕ) :
    (p.joint (fun ω=>K.kq z (by linarith only [hD]) hs (a ω) L)).i7
      (fun v i=>aR (f i) (z (a v.1))) Prod.snd
      (fun v i=>aR (g i) (z (a v.1))) ≤
    (p.joint (fun ω=>K.law (a ω))).i7
      (fun v i=>aR (f i) (z (a v.1+v.2.val)))
      (fun v=>cw z L (a v.1+v.2.val))
      (fun v i=>aR (g i) (z (a v.1+v.2.val)))+
      2*(Real.log 36+2*Real.log (D*K.bound)):=by
  let P:=p.joint (fun ω=>K.law (a ω))
  let X:=fun v:Ω × Fin (K.bound+1)=>z (a v.1)
  let Y:=fun v:Ω × Fin (K.bound+1)=>z (a v.1+v.2.val)
  let S:=fun v=>Y v-X v
  let W:=fun v:Ω × Fin (K.bound+1)=>cw z L (a v.1+v.2.val)
  have UG:=aD.P8 p (fun ω=>K.law (a ω))
    (fun ω=>K.lV z (by linarith only [hD]) hs (a ω) L)
    (fun ω i=>aR (f i) (z (a ω))) (fun ω i=>aR (g i) (z (a ω)))
  change (p.joint (fun ω=>K.kq z (by linarith only [hD]) hs (a ω) L)).i7 _ _ _=_ at UG
  rw [UG]
  have he:=P.Bp
    (fun v i=>aR (f i) (X v)) (fun v i=>aR (f i) (X v))
    (fun v=>K.lV z (by linarith only [hD]) hs (a v.1) L v.2)
    (fun v=>(S v,W v))
    (fun v i=>aR (g i) (X v)) (fun v i=>aR (g i) (X v))
    (fun _ _=>Iff.rfl) (fun v w=>by
      simp only [aO.lV,Prod.mk.injEq,Subtype.mk.injEq,
        aO.l8,oR]
      rfl) (fun _ _=>Iff.rfl)
  change P.i7 _ _ _≤_
  rw [he]
  have ht:=P.Pw (fun v i=>aR (f i) (X v))
    (fun v i=>aR (g i) (X v)) (fun v i=>aR (f i) (Y v))
    (fun v i=>aR (g i) (Y v)) W S
    (k4 g X Y) (by
      intro v w
      have hf:=k4 f X Y v w
      have hg:=k4 g X Y v w
      simp only [Prod.mk.injEq,S] at hf hg ⊢
      tauto)
  have hc:P.Hf S≤Real.log 36+2*Real.log (D*K.bound):=by
    apply je
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
    · intro v
      simpa only [S,X,Y,Nat.add_zero] using g8 z (by linarith only [hD]) hs
        (a v.1) K.bound v.2.val 0 (by omega) (by omega)
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)))
lemma Jt {ι:Type c9} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f:ι → ℝ) (i:ι) :
    (𝔼 π:Equiv.Perm ι,f (π i))=𝔼 j,f j:=by
  have hf (π:Equiv.Perm ι):(𝔼 j,f (π j))=𝔼 j,f j:=by
    rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,Equiv.sum_comp π]
  calc
    _ = 𝔼 j:ι,𝔼 π:Equiv.Perm ι,f (π j):=by
      simp_rw [← r8 f i]
      rw [Fintype.expect_const]
    _ = 𝔼 π:Equiv.Perm ι,𝔼 j,f (π j):=Finset.expect_comm _ _ _
    _ = _:=by simp_rw [hf]; rw [Fintype.expect_const]
noncomputable def aE.eW (s:aE) {b:ℕ} (hb:b≤ s.primes.card)
    (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) (j:Fin b) :
    s.bZ:=(σ,π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩)
lemma aE.s6 (s:aE) (hne:s.primes.Nonempty)
    {b:ℕ} (hb:b≤ s.primes.card) (f:s.bZ → ℝ) :
    (𝔼 σ:Fin s.primes.card → Bool,𝔼 π:Equiv.Perm (Fin s.primes.card),
      ∑ j:Fin b,f (s.eW hb σ π j)) =
    (b:ℝ)*(𝔼 i:s.bZ,f i):=by
  have:Nonempty (Fin s.primes.card):=⟨⟨0,hne.card_pos⟩⟩
  have hf (σ:Fin s.primes.card → Bool) (j:Fin b) :
      (𝔼 π:Equiv.Perm (Fin s.primes.card),f (s.eW hb σ π j))=
        𝔼 i:Fin s.primes.card,f (σ,i):=by
    exact Jt (fun i=>f (σ,i)) ⟨j.val,lt_of_lt_of_le j.isLt hb⟩
  simp only [Finset.expect_sum_comm,hf,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,← Finset.mul_expect,← Finset.univ_product_univ,Finset.expect_product]
lemma D5 {Ω:Type bU} {α:Type cD} {k b:ℕ} (hb:b≤k)
    (X:Ω → Fin k → α) (π:Equiv.Perm (Fin k)) (ω ν:Ω) :
    (fun j:Fin b=>X ω (π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩))=
      (fun j:Fin b=>X ν (π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩)) ↔
    aD.aF X π b ω=aD.aF X π b ν:=by
  constructor
  · intro h
    funext i
    by_cases hi:i.val<b
    · have hh:=congrFun h ⟨i.val,hi⟩
      simpa only [aD.aF,hi,ite_true,Option.some.injEq] using hh
    · simp only [aD.aF,hi,ite_false]
  · intro h
    funext j
    have hh:=congrFun h ⟨j.val,lt_of_lt_of_le j.isLt hb⟩
    simpa only [aD.aF,j.isLt,ite_true,Option.some.injEq] using hh
lemma aE.Ck {Ω:Type bU} (s:aE)
    {b:ℕ} (hb:b≤ s.primes.card) (σ:Fin s.primes.card → Bool)
    (π:Equiv.Perm (Fin s.primes.card)) (Z:Ω → GaussianInt) (ω ν:Ω) :
    (fun j=>s.residue (s.eW hb σ π j) (Z ω))=
      (fun j=>s.residue (s.eW hb σ π j) (Z ν)) ↔
    aD.aF (fun v=>s.bC σ (Z v)) π b ω=
      aD.aF (fun v=>s.bC σ (Z v)) π b ν:=by
  rw [funext_iff]
  simp only [s.E3]
  change (∀ j:Fin b,s.bC σ (Z ω) (π ⟨j.val,_⟩)=
    s.bC σ (Z ν) (π ⟨j.val,_⟩)) ↔ _
  rw [← funext_iff]
  exact D5 hb (fun v=>s.bC σ (Z v)) π ω ν
lemma aE.Bq {Ω:Type bU} [Fintype Ω]
    (s:aE) (p:aD Ω) (Z:Ω → GaussianInt)
    {b:ℕ} (hb:b≤ s.primes.card) :
    (𝔼 σ:Fin s.primes.card → Bool,𝔼 π:Equiv.Perm (Fin s.primes.card),
      p.Hf (fun ω j=>s.residue (s.eW hb σ π j) (Z ω)))=
    s.aV p Z b:=by
  have h (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) :=
    p.aZ _ _ (s.Ck hb σ π Z)
  simp only [h,aE.aV,aD.gP,aD.bF]
lemma aE.GZ (s:aE) (hne:s.primes.Nonempty)
    {b:ℕ} (hb:b≤ s.primes.card) :
    (𝔼 σ:Fin s.primes.card → Bool,𝔼 π:Equiv.Perm (Fin s.primes.card),
      ∑ j:Fin b,Real.log (s.bD (s.eW hb σ π j))) =
    (b:ℝ)*s.aP:=by
  rw [s.s6 hne hb (fun i=>Real.log (s.bD i))]
  simp only [← Finset.univ_product_univ,Finset.expect_product,
    aE.bD,Fintype.expect_const,aE.aP]
theorem qg {Ω:Type bU} {O:Type zV} [Fintype Ω] [Fintype O]
    (s:aE) (hne:s.primes.Nonempty) (p:aD Ω) (a:Ω → ℕ)
    (old:Ω → O) (R:aO) (z:ℕ → GaussianInt)
    (hz:Function.Injective z) (ha:∀ t,z t∈s.avoiding)
    {b L N n:ℕ} (hb:b≤ s.primes.card) {D τ A η δ E:ℝ}
    (hD:0≤D) (hτ:0≤τ) (hA:0≤A)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e:s.bZ → ℝ) (he:∀ i,0≤e i)
    (j6:∀ i,(D*L)^2<(s.bD i:ℝ)) (LI:L≤N)
    (iJ:∀ i,(L:ℝ)/(N+1)≤(τ/(s.bD i:ℝ))/2)
    (hH:(1-δ)*(b:ℝ)*s.aP≤ s.aV p (fun ω=>z (a ω)) b)
    (hO:p.Hf old≤E)
    (Bm:(𝔼 i:s.bZ,p.prob (fun ω=>e i≤
      (((R.then (dQ N)).cV s z (a ω) i).cW τ).card))≤η)
    (hnum:∀ i,Real.log (4*e i+(s.bD i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.bD i:ℝ))/2)/4))) ≤
        Real.log (s.bD i)-A) :
    (b:ℝ)*(A*(1-2*η)-δ*s.aP)-E ≤ (n:ℝ)*
      (𝔼 σ:Fin s.primes.card → Bool,𝔼 π:Equiv.Perm (Fin s.primes.card),
        (p.joint (fun ω=>(R.then (dQ N)).kq z hD hs (a ω) L)).i7
          (fun v j=>s.residue (s.eW hb σ π j) (z (a v.1)))
          Prod.snd (fun v=>old v.1)):=by
  let X:=fun (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card))
    (ω:Ω) (j:Fin b)=>s.residue (s.eW hb σ π j) (z (a ω))
  let Bad:=fun i=>p.prob (fun ω=>e i≤
    (((R.then (dQ N)).cV s z (a ω) i).cW τ).card)
  have hi (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) :=
    qd s p a old (s.eW hb σ π) R z hz ha
      hD hτ hA hs (fun j=>e (s.eW hb σ π j))
      (fun j=>he _) (fun j=>j6 _) LI (fun j=>iJ _)
      (H:=(∑ j,Real.log (s.bD (s.eW hb σ π j)))-p.bT (X σ π) old)
      (by dsimp only [X]; linarith)
      (η:=∑ j,Bad (s.eW hb σ π j)) le_rfl (fun j=>hnum _)
  have hav:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s:=Finset.univ) (fun π _=>hi σ π))
  simp only [Fintype.card_fin,Finset.expect_sub_distrib,← Finset.mul_expect,Fintype.expect_const,
    Finset.expect_sum_comm] at hav
  have hx (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) :
      p.Hf (X σ π)-E≤p.bT (X σ π) old:=by
    have h:=p.kH old (X σ π)
    rw [p.kd] at h
    unfold aD.bT
    linarith only [h,hO]
  have hxa:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s:=Finset.univ) (fun π _=>hx σ π))
  simp only [Finset.expect_sub_distrib,Fintype.expect_const] at hxa
  have hxe:=s.Bq p (fun ω=>z (a ω)) hb
  change (𝔼 σ,𝔼 π,p.Hf (X σ π))=_ at hxe
  rw [hxe] at hxa
  have hlog:=s.GZ hne hb
  have hbad:=s.s6 hne hb Bad
  have hbR:0≤(b:ℝ):=Nat.cast_nonneg _
  have Wb:(b:ℝ)*(𝔼 i,Bad i)≤b*η:=mul_le_mul_of_nonneg_left Bm hbR
  simp only [Finset.expect_sum_comm] at hlog hbad
  rw [hlog,hbad] at hav
  have hprod:=mul_le_mul_of_nonneg_left Wb hA
  nlinarith only [hav,hxa,hH,hprod]
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU qC c9 cD dD g4
namespace GaussianMoat
open scoped BigOperators Classical
theorem Br {Ω:Type bU} {κ:Type qC} [Fintype Ω]
    (s:aE) (hne:s.primes.Nonempty) (p:aD Ω) (a:Ω → ℕ)
    (g:κ → GaussianInt) (R:aO) (z:ℕ → GaussianInt)
    (hz:Function.Injective z) (ha:∀ t,z t∈s.avoiding)
    {b L N n:ℕ} (hb:b≤ s.primes.card) (hn:0<n) (hL:0<L)
    {D τ A η δ E r:ℝ} (hD:1≤D) (hτ:0≤τ) (hA:0≤A)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e:s.bZ → ℝ) (he:∀ i,0≤e i)
    (j6:∀ i,(D*L)^2<(s.bD i:ℝ)) (LI:L≤N)
    (iJ:∀ i,(L:ℝ)/(N+1)≤(τ/(s.bD i:ℝ))/2)
    (hH:(1-δ)*(b:ℝ)*s.aP≤ s.aV p (fun ω=>z (a ω)) b)
    (hO:p.Hf (fun ω i=>aR (g i) (z (a ω)))≤E)
    (Bm:(𝔼 i:s.bZ,p.prob (fun ω=>e i≤
      (((R.then (dQ N)).cV s z (a ω) i).cW τ).card))≤η)
    (hnum:∀ i,Real.log (4*e i+(s.bD i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.bD i:ℝ))/2)/4))) ≤
        Real.log (s.bD i)-A)
    (N9:(n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(R.bound+N)))) ≤
      (b:ℝ)*(A*(1-2*η)-δ*s.aP)-E) :
    ∃ σ:Fin s.primes.card → Bool,∃ π:Equiv.Perm (Fin s.primes.card),
      r≤ (p.joint (fun ω=>(R.then (dQ N)).law (a ω))).i7
        (fun v j=>aR (s.fO (s.eW hb σ π j))
          (z (a v.1+v.2.val)))
        (fun v=>cw z L (a v.1+v.2.val))
        (fun v i=>aR (g i) (z (a v.1+v.2.val))) / L:=by
  let K:=R.then (dQ N)
  let old:=fun ω i=>aR (g i) (z (a ω))
  let QG:=aD.ju old
  have QH:p.Hf QG≤E:=by
    apply le_trans (le_of_eq (p.aZ QG old (fun ω ν=>aD.gO old ω ν))) hO
  have hD0:0≤D:=by linarith only [hD]
  have Wd:=qg s hne p a QG R z hz ha hb
    hD0 hτ hA hs e he j6 LI iJ hH QH Bm hnum
  let Info:=fun (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) =>
    (p.joint (fun ω=>K.law (a ω))).i7
      (fun v j=>aR (s.fO (s.eW hb σ π j)) (z (a v.1+v.2.val)))
      (fun v=>cw z L (a v.1+v.2.val))
      (fun v i=>aR (g i) (z (a v.1+v.2.val)))
  have hK:1≤K.bound:=by change 1≤R.bound+N; omega
  have ht (σ:Fin s.primes.card → Bool) (π:Equiv.Perm (Fin s.primes.card)) :
      (p.joint (fun ω=>K.kq z hD0 hs (a ω) L)).i7
        (fun v j=>s.residue (s.eW hb σ π j) (z (a v.1))) Prod.snd
        (fun v=>QG v.1) ≤ Info σ π+2*(Real.log 36+2*Real.log (D*K.bound)):=by
    have hc:=(p.joint (fun ω=>K.kq z hD0 hs (a ω) L)).Bp
      (fun v j=>s.residue (s.eW hb σ π j) (z (a v.1)))
      (fun v j=>aR (s.fO (s.eW hb σ π j)) (z (a v.1)))
      Prod.snd Prod.snd (fun v=>QG v.1) (fun v=>old v.1)
      (fun v w=>by
        simp only [funext_iff,aE.residue,jX,k9])
      (fun _ _=>Iff.rfl) (fun v w=>aD.gO old v.1 w.1)
    rw [hc]
    exact K.tJ p a (fun j=>s.fO (s.eW hb σ π j))
      g z hD hs hK L
  have hav:=Finset.expect_le_expect (s:=Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s:=Finset.univ) (fun π _=>ht σ π))
  simp only [Finset.expect_add_distrib,Fintype.expect_const] at hav
  have hmul:=mul_le_mul_of_nonneg_left hav (Nat.cast_nonneg n)
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have Wf:(L:ℝ)*r≤𝔼 σ,𝔼 π,Info σ π:=by
    have heK:(K.bound:ℝ)=R.bound+N:=by simp only [K,aO.then,dQ,Nat.cast_add]
    conv at hmul=>rhs; rw [heK]
    have hh:=N9.trans (Wd.trans hmul)
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [hh]
  obtain ⟨σ,_,hσ⟩:=Finset.exists_le_of_le_expect Finset.univ_nonempty Wf
  obtain ⟨π,_,hπ⟩:=Finset.exists_le_of_le_expect Finset.univ_nonempty hσ
  refine ⟨σ,π,?_⟩
  exact (le_div_iff₀ (show (0:ℝ)<L by exact_mod_cast hL)).mpr (by simpa only [mul_comm] using hπ)
lemma Bv (n:ℕ) (a b:ℕ → ℝ) (ε:ℝ)
    (hnext:∀ j<n,a (j+1)≤b j+ε) (hb:0≤b n) :
    (∑ j∈Finset.range (n+1),(a j-b j)) ≤ a 0+n*ε:=by
  have h:(∑ j∈Finset.range (n+1),(a j-b j)) ≤ a 0+n*ε-b n:=by
    clear hb
    induction n with
    | zero=>simp
    | succ n ih =>
      have hn:=ih (fun j hj=>hnext j (by omega))
      have hh:=hnext n (by omega)
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      linarith only [hn,hh]
  linarith only [h,hb]
theorem w9 {Ω:Type bU} {ι:Type c9} [Fintype Ω] [Fintype ι]
    (p:aD Ω) (t:Ω → ℕ) (z:ℕ → GaussianInt) {D:ℝ}
    (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f:ι → GaussianInt) (hf:∀ i,f i≠0) {L K N:ℕ}
    (hL:0<L) (hK:0<K) (hdiv:L∣K) (hKN:K≤N) {ε:ℝ} (hε:0≤ε)
    (iJ:∀ a<K,2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (bY D).card+
        2*∑ i,Real.log (f i).norm.natAbs) ≤ ε) :
    let P:=p.joint (fun _=>aD.uniform (Fin (N+1)))
    P.bT (fun v=>cw z K (t v.1+v.2.val))
      (fun v i=>aR (f i) (z (t v.1+v.2.val))) / K ≤
    P.bT (fun v=>cw z L (t v.1+v.2.val))
      (fun v i=>aR (f i) (z (t v.1+v.2.val))) / L + ε:=by
  dsimp only
  let P:=p.joint (fun _=>aD.uniform (Fin (N+1)))
  let u:=fun v:Ω × Fin (N+1)=>t v.1+v.2.val
  let Q:=fun v i=>aR (f i) (z (u v))
  let H:=P.bT (fun v=>cw z L (u v)) Q
  obtain ⟨m,hm⟩:=hdiv
  have hm':K=m*L:=by simpa [Nat.mul_comm] using hm
  have hmp:0 < m:=by nlinarith only [hK,hm]
  have hLp:(0:ℝ)<L:=by exact_mod_cast hL
  have hmR:(0:ℝ) < m:=by exact_mod_cast hmp
  have JX:=vq P u z f L m hL
  have hsum:(∑ j:Fin m,P.bT (fun v=>cw z L (u v+j.val*L))
      (fun v i=>aR (f i) (z (u v+j.val*L)))) ≤ (m:ℝ)*(H+ε):=by
    have hh (j:Fin m):P.bT (fun v=>cw z L (u v+j.val*L))
        (fun v i=>aR (f i) (z (u v+j.val*L))) ≤ H+ε:=by
      have hj:j.val*L<K:=by rw [hm']; exact Nat.mul_lt_mul_of_pos_right j.isLt hL
      have hs:=DY p t z hz f hf L N (j.val*L) (by omega)
      dsimp only at hs
      change P.bT _ _ ≤ H+_+_ at hs
      have he:=iJ (j.val*L) hj
      linarith only [hs,he]
    have hh':=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>hh j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh'
  have Aa:=JX.trans hsum
  have hd:=div_le_div_of_nonneg_right Aa (show (0:ℝ)≤ m*L by positivity)
  have he:(m:ℝ)*(H+ε)/((m:ℝ)*L)=(H+ε)/L:=by field_simp
  rw [he,add_div] at hd
  have hel:ε/(L:ℝ)≤ε:=div_le_self hε (by exact_mod_cast hL)
  rw [hm',Nat.cast_mul]
  change P.bT (fun v=>cw z (m*L) (u v)) Q / ((m:ℝ)*L) ≤ H/L+ε
  linarith only [hd,hel]
lemma aD.OQ {Ω:Type bU} {α:Type cD} {β:Type dD} {γ:Type g4} [Fintype Ω]
    (p:aD Ω) (X:Ω → α) (Y:Ω → β) (O:Ω → γ)
    (h:∀ ω ν,X ω = X ν → O ω = O ν) :
    p.i7 X Y O = p.bT Y O - p.bT Y X:=by
  rw [p.oO]
  unfold aD.i7
  congr 1
  apply p.jB Y Y (fun ω=>(O ω,X ω)) X
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hx=>⟨h ω ν hx,hx⟩⟩
theorem qX {Ω:Type bU} [Fintype Ω]
    (p:aD Ω) (t:Ω → ℕ) (z:ℕ → GaussianInt) {D:ℝ}
    (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (F:ℕ → Finset GaussianInt) (hF:∀ j,F j ⊆ F (j+1))
    (hf:∀ j,∀ f ∈ F j,f ≠ 0) (L:ℕ → ℕ) (n N:ℕ)
    (hL:∀ j ≤ n,0 < L j) (hdiv:∀ j < n,L j ∣ L (j+1))
    (hN:∀ j ≤ n,L j ≤ N) {ε:ℝ} (hε:0 ≤ ε)
    (iJ:∀ j < n,∀ a < L (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1)) + ((a:ℝ)/(N+1))*
        ((L j:ℝ)*Real.log (bY D).card +
          2*∑ f ∈ F (j+1),Real.log f.norm.natAbs) ≤ ε) :
    let P:=p.joint (fun _=>aD.uniform (Fin (N+1)))
    let u:=fun v:Ω × Fin (N+1)=>t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.i7 (fun v (f:F (j+1))=>aR f.val (z (u v)))
        (fun v=>cw z (L j) (u v))
        (fun v (f:F j)=>aR f.val (z (u v))) / L j) ≤
      Real.log (bY D).card + n*ε:=by
  dsimp only
  let P:=p.joint (fun _=>aD.uniform (Fin (N+1)))
  let u:=fun v:Ω × Fin (N+1)=>t v.1+v.2.val
  let Q:=fun j=>fun v (f:F j)=>aR f.val (z (u v))
  let a:=fun j=>P.bT (fun v=>cw z (L j) (u v)) (Q j) / L j
  let b:=fun j=>P.bT (fun v=>cw z (L j) (u v)) (Q (j+1)) / L j
  have hnext (j:ℕ) (hj:j < n):a (j+1) ≤ b j+ε:=by
    dsimp only [a,b,Q,u,P]
    apply w9 p t z hz (fun f:F (j+1)=>f.val)
      (fun f=>hf _ _ f.property) (hL j (by omega)) (hL (j+1) (by omega))
      (hdiv j hj) (hN (j+1) (by omega)) hε
    intro k hk
    convert iJ j hj k hk using 1
    rw [Finset.sum_coe_sort (F (j+1)) (fun f:GaussianInt=>Real.log f.norm.natAbs)]
  have hb:0 ≤ b n:=div_nonneg (P.F7 _ _) (Nat.cast_nonneg _)
  have hi (j:ℕ):P.i7 (Q (j+1)) (fun v=>cw z (L j) (u v)) (Q j) /
      L j = a j-b j:=by
    rw [P.OQ,sub_div]
    intro v w hv
    funext f
    exact congrFun hv ⟨f.val,hF j f.property⟩
  have ht:=Bv n a b ε hnext hb
  have ha:a 0 ≤ Real.log (bY D).card:=by
    apply (div_le_iff₀ (show (0:ℝ) < L 0 by exact_mod_cast hL 0 (by omega))).mpr
    have hh:=(P.C8 (fun v=>cw z (L 0) (u v)) (Q 0)).trans
      (DU P u z hz (L 0))
    simpa only [mul_comm] using hh
  change (∑ j ∈ Finset.range (n+1),P.i7 (Q (j+1))
    (fun v=>cw z (L j) (u v)) (Q j) / L j) ≤ _
  simp only [hi]
  linarith only [ht,ha]
noncomputable def bR.info {α:Type cD} {β:Type dD} {γ:Type g4} (P:bR)
    (X:ℕ → α) (Y:ℕ → β) (O:ℕ → γ):ℝ :=
  P.law.i7 (fun t=>X t.val) (fun t=>Y t.val) (fun t=>O t.val)
lemma bR.Ku {α:Type cD} {β:Type dD} {γ:Type g4} (P:bR) (K:aO)
    (X:ℕ → α) (Y:ℕ → β) (O:ℕ → γ) :
    (P.advance K).info X Y O=(P.law.joint (fun a=>K.law a.val)).i7
      (fun v=>X (v.1.val+v.2.val)) (fun v=>Y (v.1.val+v.2.val))
      (fun v=>O (v.1.val+v.2.val)):=by
  unfold bR.info bR.advance
  rw [aD.OP]
  rfl
lemma m9 (z:ℕ → GaussianInt) (ns:List ℕ) (N:ℕ) :
    b9 z ns N=(b9 z ns 0).then (dQ N):=by
  simpa only [List.append_nil,b9,List.foldr_nil] using m8 z ns [] N
theorem s7 (z:ℕ → GaussianInt) {D:ℝ}
    (hz:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D) (ns:List ℕ) (N n:ℕ)
    (F:ℕ → Finset GaussianInt) (hF:∀ j,F j⊆F (j+1))
    (hf:∀ j,∀ f∈F j,f≠0) (L:ℕ → ℕ)
    (hL:∀ j≤n,0<L j) (hdiv:∀ j<n,L j∣L (j+1)) (hN:∀ j≤n,L j≤N)
    {ε:ℝ} (hε:0≤ε)
    (iJ:∀ j<n,∀ a<L (j+1),2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (bY D).card+
        2*∑ f∈F (j+1),Real.log f.norm.natAbs)≤ε) :
    let P:=(bR.at 0).advance (b9 z ns N)
    (∑ j∈Finset.range (n+1),P.info
      (fun a (f:F (j+1))=>aR f.val (z a)) (cw z (L j))
      (fun a (f:F j)=>aR f.val (z a)) / L j)≤
        Real.log (bY D).card+n*ε:=by
  let Q:=(bR.at 0).advance (b9 z ns 0)
  have h:=qX Q.law (fun t=>t.val) z hz F hF hf L n N
    hL hdiv hN hε iJ
  dsimp only
  rw [m9,bR.Bd]
  simp only [bR.Ku]
  exact h
theorem xg (s:aE) (hne:s.primes.Nonempty)
    (z:ℕ → GaussianInt) (hz:Function.Injective z) (ha:∀ t,z t∈s.avoiding)
    (pre rest:List ℕ) {N b L n:ℕ} {D T τ A η δ E r:ℝ}
    (hD:1≤D) (hT:5≤T) (hML:1≤ s.aP)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (DZ:fq s D pre 0 b δ)
    (u:s.bZ → ℝ) (coverage:gG s D N rest τ u η)
    {κ:Type qC} (f:κ → GaussianInt)
    (QH:((bR.at 0).advance (b9 z pre 0)).law.Hf
      (fun t i=>aR (f i) (z t.val))≤E)
    (hb:b≤ s.primes.card) (hn:0<n) (hL:0<L) (hτ:0≤τ) (hA:0≤A)
    (hu:∀ i,0≤u i) (j6:∀ i,(D*L)^2<(s.bD i:ℝ)) (LI:L≤N)
    (iJ:∀ i,(L:ℝ)/(N+1)≤(τ/(s.bD i:ℝ))/2)
    (hnum:∀ i,Real.log (4*u i+(s.bD i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.bD i:ℝ))/2)/4)))≤Real.log (s.bD i)-A)
    (N9:(n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.aP)-E) :
    ∃ σ:Fin s.primes.card → Bool,∃ π:Equiv.Perm (Fin s.primes.card),
      r≤((bR.at 0).advance (b9 z (pre++rest) N)).info
        (fun a j=>aR (s.fO (s.eW hb σ π j)) (z a))
        (cw z L) (fun a i=>aR (f i) (z a)) / L:=by
  let P:=(bR.at 0).advance (b9 z pre 0)
  let R:=b9 z rest 0
  have hH:(1-δ)*(b:ℝ)*s.aP≤ s.aV P.law (fun t=>z t.val) b:=by
    rw [aE.oP]
    simpa only [Nat.zero_add] using DZ.sound hne z hz hD hT hs hpT hML 0
  have hc:=coverage.sound hne z hz hD hT hs hpT hML
  have Bm:(𝔼 i:s.bZ,P.law.prob (fun ω=>u i≤
      (((R.then (dQ N)).cV s z ω.val i).cW τ).card))≤η:=by
    let:=s.dY hne
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun ω _ =>
      mul_le_mul_of_nonneg_left (hc ω.val) (P.law.nonneg ω))
    simp only [← Finset.sum_mul,P.law.dN,one_mul] at hh
    rw [← m9]
    unfold aD.prob at hh ⊢
    rw [Finset.expect_eq_sum_div_card]
    simp only [aD.uniform,Finset.mul_sum,mul_ite,mul_zero] at hh
    rw [Finset.sum_comm] at hh
    convert hh using 1
    all_goals first | rfl | simp only [Finset.card_univ,div_eq_mul_inv,Finset.sum_mul,ite_mul,zero_mul]
  obtain ⟨σ,π,hh⟩:=Br s hne P.law (fun t=>t.val) f R z hz ha
    hb hn hL hD hτ hA hs u hu j6 LI iJ hH QH Bm hnum
    (by simpa only [R,jG,Nat.add_zero] using N9)
  refine ⟨σ,π,?_⟩
  have heR:b9 z rest N=R.then (dQ N):=m9 z rest N
  rw [m8,bR.Bd,bR.Ku,heR]
  exact hh
end GaussianMoat
end OAI
end
section
namespace OAI
universe bU c9 dD
namespace GaussianMoat
open scoped BigOperators Classical
noncomputable def mK (p:ℕ):GaussianInt :=
  if h:p.Prime ∧ p%4=1 then (tQ h.1 h.2).choose else 0
lemma qI {p:ℕ} (hp:p.Prime) (hm:p%4=1) :
    Irreducible (mK p) ∧ (mK p).norm=(p:ℤ):=by
  rw [mK,JG ⟨hp,hm⟩]
  exact (tQ hp hm).choose_spec
noncomputable def Kw (S:Finset ℕ)
    (hS:∀ p∈S,p.Prime ∧ p%4=1):aE where
  primes:=S
  factor:=mK
  iF:=fun p hp=>(hS p hp).1
  Fy:=fun p hp=>(hS p hp).2
  jA:=fun p hp=>(qI (hS p hp).1 (hS p hp).2).1
  jc:=fun p hp=>(qI (hS p hp).1 (hS p hp).2).2
noncomputable def cP (j:ℕ):aE :=
  Kw (dS.d6 j) (fun p hp=>by
    have h:=(dS.iw j p).mp hp
    exact ⟨h.2.2.1,h.2.2.2⟩)
lemma lJ (f:GaussianInt):0≤Real.log f.norm.natAbs:=by
  by_cases h:f.norm.natAbs=0
  · simp only [h,Nat.cast_zero,Real.log_zero,le_refl]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
noncomputable def c8 (F:Finset GaussianInt):ℝ :=
  ∑ f∈F,Real.log f.norm.natAbs
lemma oT {F G:Finset GaussianInt} (h:F⊆G):c8 F≤c8 G :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun f _ _=>lJ f)
lemma G7 (F:Finset GaussianInt):0≤c8 F :=
  Finset.sum_nonneg (fun f _=>lJ f)
theorem D6 {Ω:Type bU} {ι:Type c9} [Fintype Ω] [Fintype ι]
    (p:aD Ω) (z:Ω → GaussianInt) (f:ι → GaussianInt) (hf:∀ i,f i≠0) :
    p.Hf (fun ω i=>aR (f i) (z ω))≤∑ i,Real.log (f i).norm.natAbs:=by
  let (i:ι):Finite (GaussianInt ⧸ multiples (f i)):=kN (hf i)
  let (i:ι):Fintype (GaussianInt ⧸ multiples (f i)):=Fintype.ofFinite _
  rw [p.aZ _ (fun ω i=>aY (f i) (z ω))
    (fun ω ν=>oz f (z ω) (z ν))]
  have hh:=p.kF (fun ω i=>aY (f i) (z ω))
  rw [Fintype.card_pi,Nat.cast_prod,Real.log_prod] at hh
  · convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.card_eq_fintype_card,l5 (hf i)]
  · intro i _
    exact_mod_cast Fintype.card_ne_zero
lemma D7 {Ω:Type bU} [Fintype Ω] (p:aD Ω)
    (z:Ω → GaussianInt) (F:Finset GaussianInt) (hf:∀ f∈F,f≠0) :
    p.Hf (fun ω (f:F)=>aR f.val (z ω))≤c8 F:=by
  have h:=D6 p z (fun f:F=>f.val) (fun f=>hf f.val f.property)
  exact h.trans_eq (Finset.sum_subtype F (fun _=>Iff.rfl)
    (fun f:GaussianInt=>Real.log f.norm.natAbs)).symm
noncomputable def aE.e6 (s:aE):Finset GaussianInt :=
  Finset.univ.image (fun i:s.primes × Bool=>dG (s.factor i.1.val) i.2)
lemma aE.G8 (s:aE) (i:s.bZ) :
    s.fO i∈s.e6:=by
  exact Finset.mem_image.mpr ⟨(s.enumeration i.2,i.1 i.2),Finset.mem_univ _,rfl⟩
lemma aE.Ls (s:aE) {f:GaussianInt} (hf:f∈s.e6) :
    f≠0:=by
  obtain ⟨⟨p,b⟩,_,rfl⟩:=Finset.mem_image.mp hf
  intro h
  have hn:=(iW (s.factor p.val) b).trans (s.jc p.val p.property)
  rw [h] at hn
  have hp:=(s.iF p.val p.property).ne_zero
  apply hp
  simpa only [Zsqrtd.norm_zero,Nat.cast_eq_zero] using hn.symm
lemma aE.MZ (s:aE) :
    c8 s.e6≤2*∑ p∈s.primes,Real.log (p:ℝ):=by
  have hh:=Finset.sum_image_le_of_nonneg (s:=(Finset.univ:Finset (s.primes × Bool)))
    (g:=fun i:s.primes × Bool=>dG (s.factor i.1.val) i.2)
    (f:=fun f:GaussianInt=>Real.log f.norm.natAbs) (fun f _=>lJ f)
  change c8 s.e6≤_ at hh
  apply hh.trans_eq
  simp only [Fintype.sum_prod_type,iW]
  simp only [s.jc _ (Subtype.property _),Int.natAbs_natCast]
  simp only [Fintype.sum_bool,Finset.sum_add_distrib]
  rw [← Finset.sum_subtype s.primes (fun _=>Iff.rfl) (fun p:ℕ=>Real.log (p:ℝ))]
  ring
lemma aD.M4 {Ω:Type bU} {ι:Type c9} {β:Type dD} [Fintype Ω] [Fintype ι]
    (p:aD Ω) (z:Ω → GaussianInt) (Y:Ω → β)
    (F:Finset GaussianInt) (f:ι → GaussianInt) :
    p.i7 (fun ω (g:↥(F∪Finset.univ.image f))=>aR g.val (z ω)) Y
      (fun ω (g:F)=>aR g.val (z ω))=
    p.i7 (fun ω i=>aR (f i) (z ω)) Y
      (fun ω (g:F)=>aR g.val (z ω)):=by
  rw [p.oO,p.oO (fun ω i=>aR (f i) (z ω))]
  unfold aD.i7
  congr 1
  apply p.jB
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hO,hU⟩
      refine ⟨hO,funext fun i=>?_⟩
      exact congrFun hU ⟨f i,Finset.mem_union_right F (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩
    · rintro ⟨hO,hU⟩
      refine ⟨hO,funext fun g=>?_⟩
      rcases Finset.mem_union.mp g.property with hg|hg
      · exact congrFun hO ⟨g.val,hg⟩
      · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hg
        simpa only [hi] using congrFun hU i
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
section
open scoped BigOperators Classical
structure kL (D:ℝ) (ns:List ℕ) (N:ℕ) (s:aE)
    (L:ℕ) (E r:ℝ) where
  pre:List ℕ
  rest:List ℕ
  schedule:ns=pre++rest
  T:ℝ
  nonempty:s.primes.Nonempty
  LJ:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T
  large:5≤T
  mean:1≤ s.aP
  b:ℕ
  n:ℕ
  τ:ℝ
  A:ℝ
  η:ℝ
  δ:ℝ
  u:s.bZ → ℝ
  DZ:fq s D pre 0 b δ
  coverage:gG s D N rest τ u η
  cap:b≤ s.primes.card
  repetitions:0<n
  length:0<L
  floor:0≤τ
  gain:0≤A
  exceptions:∀ i,0≤u i
  short:∀ i,(D*L)^2<(s.bD i:ℝ)
  xB:L≤N
  Ky:∀ i,(L:ℝ)/(N+1)≤(τ/(s.bD i:ℝ))/2
  list:∀ i,Real.log (4*u i+(s.bD i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.bD i:ℝ))/2)/4)))≤Real.log (s.bD i)-A
  rate:(n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.aP)-E
theorem kL.sound {D E r:ℝ} {ns:List ℕ} {N L:ℕ} {s:aE}
    (q:kL D ns N s L E r) (hD:1≤D)
    (z:ℕ → GaussianInt) (hz:Function.Injective z) (ha:∀ t,z t∈s.avoiding)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (F:Finset GaussianInt) (hf:∀ f∈F,f≠0) (hF:c8 F≤E) :
    ∃ G:Finset GaussianInt,F⊆G ∧ G⊆F∪s.e6 ∧
      r≤((bR.at 0).advance (b9 z ns N)).info
        (fun a (f:G)=>aR f.val (z a)) (cw z L)
        (fun a (f:F)=>aR f.val (z a)) / L:=by
  let Q:=(bR.at 0).advance (b9 z q.pre 0)
  have QH:Q.law.Hf (fun t (f:F)=>aR f.val (z t.val))≤E :=
    (D7 Q.law (fun t=>z t.val) F hf).trans hF
  obtain ⟨σ,π,hh⟩:=xg s q.nonempty z hz ha q.pre q.rest hD q.large
    q.mean hs q.LJ q.DZ q.u q.coverage (fun f:F=>f.val) QH
    q.cap q.repetitions q.length q.floor q.gain q.exceptions q.short q.xB
    q.Ky q.list q.rate
  let f:=fun j=>s.fO (s.eW q.cap σ π j)
  let G:=F∪Finset.univ.image f
  refine ⟨G,Finset.subset_union_left,?_,?_⟩
  · apply Finset.union_subset Finset.subset_union_left
    intro g hg
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hg
    exact Finset.mem_union_right F (s.G8 _)
  · rw [q.schedule]
    unfold bR.info
    rw [aD.M4]
    exact hh
theorem Cm (A:ℕ → Finset GaussianInt)
    (hA:∀ j,A j⊆A (j+1)) (n:ℕ)
    (R:ℕ → Finset GaussianInt → Finset GaussianInt → Prop)
    (hstep:∀ j≤n,∀ F⊆A j,∃ G,F⊆G ∧ G⊆A (j+1) ∧ R j F G) :
    ∃ F:ℕ → Finset GaussianInt,
      (∀ j,F j⊆A j) ∧ (∀ j,F j⊆F (j+1)) ∧ (∀ j≤n,R j (F j) (F (j+1))):=by
  have step (j:ℕ) (F:{F:Finset GaussianInt // F⊆A j}) :
      ∃ G:{G:Finset GaussianInt // G⊆A (j+1)},F.val⊆G.val ∧ (j≤n → R j F.val G.val):=by
    by_cases hj:j≤n
    · obtain ⟨G,hFG,hG,hR⟩:=hstep j hj F.val F.property
      exact ⟨⟨G,hG⟩,hFG,fun _=>hR⟩
    · exact ⟨⟨F.val,F.property.trans (hA j)⟩,Finset.Subset.refl _,fun h=>(hj h).elim⟩
  let f (j:ℕ) (F:{F:Finset GaussianInt // F⊆A j}):=(step j F).choose
  let F:(j:ℕ) → {F:Finset GaussianInt // F⊆A j} :=
    @Nat.rec (fun j=>{F:Finset GaussianInt // F⊆A j}) ⟨∅,Finset.empty_subset _⟩ f
  refine ⟨fun j=>(F j).val,fun j=>(F j).property,?_,?_⟩
  · intro j
    exact (step j (F j)).choose_spec.1
  · intro j hj
    exact (step j (F j)).choose_spec.2 hj
noncomputable def gd (s:ℕ → aE) (j:ℕ):Finset GaussianInt :=
  (Finset.range j).biUnion (fun i=>(s i).e6)
lemma rD (s:ℕ → aE) {i j:ℕ} (h:i≤j) :
    gd s i⊆gd s j :=
by
  intro f hf
  obtain ⟨k,hk,hf⟩:=Finset.mem_biUnion.mp hf
  exact Finset.mem_biUnion.mpr ⟨k,(Finset.range_mono h) hk,hf⟩
lemma Fh (s:ℕ → aE) (j:ℕ) :
    gd s (j+1)=gd s j∪(s j).e6:=by
  simp only [gd,Finset.range_add_one,Finset.biUnion_insert,Finset.union_comm]
lemma oW (s:ℕ → aE) {j:ℕ} {f:GaussianInt}
    (h:f∈gd s j):f≠0:=by
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp h
  exact (s i).Ls hi
theorem Ju {D ε:ℝ} (hD:1≤D) (ns:List ℕ) (N n:ℕ)
    (s:ℕ → aE) (L:ℕ → ℕ) (r:ℕ → ℝ)
    (cert:∀ j≤n,kL D ns N (s j) (L j)
      (c8 (gd s j)) (r j))
    (hdiv:∀ j<n,L j∣L (j+1)) (hε:0≤ε)
    (iJ:∀ j<n,∀ a<L (j+1),2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (bY D).card+
        2*c8 (gd s (n+1)))≤ε)
    (zU:Real.log (bY D).card+n*ε<∑ j∈Finset.range (n+1),r j)
    (z:ℕ → GaussianInt) (hz:Function.Injective z)
    (ha:∀ j≤n,∀ t,z t∈(s j).avoiding)
    (hs:∀ t,dist (z t:ℂ) (z (t+1):ℂ)≤D):False:=by
  let P:=(bR.at 0).advance (b9 z ns N)
  let rate (j:ℕ) (F G:Finset GaussianInt):=P.info
    (fun a (f:G)=>aR f.val (z a)) (cw z (L j))
    (fun a (f:F)=>aR f.val (z a)) / L j
  obtain ⟨F,hFA,hFF,hR⟩:=Cm (gd s)
    (fun j=>rD s (Nat.le_succ j)) n
    (fun j F G=>r j≤rate j F G) (by
      intro j hj F hF
      obtain ⟨G,hFG,hG,hI⟩:=(cert j hj).sound hD z hz (ha j hj) hs F
        (fun f hf=>oW s (hF hf)) (oT hF)
      refine ⟨G,hFG,?_,hI⟩
      rw [Fh]
      exact hG.trans (Finset.union_subset_union_left hF))
  have ht:=s7 z hs ns N n F hFF
    (fun j f hf=>oW s (hFA j hf)) L
    (fun j hj=>(cert j hj).length) hdiv (fun j hj=>(cert j hj).xB) hε (by
      intro j hj a ha
      have hw:=oT ((hFA (j+1)).trans (rD s (j:=n+1) (by omega)))
      have hh:=iJ j hj a ha
      have hx:0≤(a:ℝ)/(N+1):=by positivity
      change _+_ * (_+2*c8 (F (j+1)))≤ε
      nlinarith only [hw,hh,hx])
  have hh:=Finset.sum_le_sum (s:=Finset.range (n+1)) (fun j hj=>hR j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj))
  exact (not_lt_of_ge (hh.trans ht)) zU
open scoped BigOperators Classical
open Filter
theorem O6 (J:Finset ℕ) {K:ℕ} (hK:0<K) :
    ∃ a<K,((J.card:ℝ)/K)≤(J.filter (fun j=>j%K=a)).card ∧
      ∀ i∈J.filter (fun j=>j%K=a),∀ j∈J.filter (fun j=>j%K=a),
        i<j → i+K≤j:=by
  have hh:(Finset.range K).card • ((J.card:ℝ)/K)≤(J.card:ℝ):=by
    rw [Finset.card_range,nsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hK.ne')]
  obtain ⟨a,ha,hc⟩:=Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s:=J) (t:=Finset.range K) (f:=fun j=>j%K)
    (fun j _=>Finset.mem_range.mpr (Nat.mod_lt _ hK))
    (Finset.nonempty_range_iff.mpr hK.ne') hh
  refine ⟨a,Finset.mem_range.mp ha,hc,?_⟩
  intro i hi j hj hij
  have hi':=(Finset.mem_filter.mp hi).2
  have hj':=(Finset.mem_filter.mp hj).2
  have hd:i%K=j%K:=hi'.trans hj'.symm
  have hei:=Nat.mod_add_div i K
  have XB:=Nat.mod_add_div j K
  have hq:i/K<j/K:=by nlinarith only [hei,XB,hd,hij]
  nlinarith only [hei,XB,hd,hq]
theorem M8 (K:ℕ) (hK:0<K) :
    ∃ c δ:ℝ,0<c ∧ 0<δ ∧ ∀ᶠ X:ℝ in atTop,∃ J:Finset ℕ,
      c*X≤J.card ∧
      (∀ i∈J,∀ j∈J,i<j → i+K≤j) ∧
      ∀ j∈J,X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card:=by
  obtain ⟨c,δ,hc,hδ,he⟩:=dS.nF
  refine ⟨c/K,δ,div_pos hc (by exact_mod_cast hK),hδ,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩:=hX
  obtain ⟨a,_,hcard,hsep⟩:=O6 J hK
  refine ⟨J.filter (fun j=>j%K=a),?_,hsep,?_⟩
  · have hh:=(div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1
lemma nC (j:ℕ) :
    c8 (cP j).e6≤4*Real.log 4*(2:ℝ)^j:=by
  have hp:(∑ p∈dS.d6 j,Real.log (p:ℝ))≤Real.log 4*(2:ℝ)^(j+1) :=
    dS.pN _ (by positivity) (by
      intro p hp
      have h:=(dS.iw j p).mp hp
      exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  have hh:=(cP j).MZ
  change c8 (cP j).e6≤2*∑ p∈dS.d6 j,Real.log (p:ℝ) at hh
  rw [pow_succ] at hp
  nlinarith only [hh,hp]
end
open scoped BigOperators Classical
lemma P9 (g U:ℝ) (j k:ℕ) :
    aW g U (j+k)=aW g (aW g U j) k:=by
  unfold aW
  rw [pow_add]
  ring
lemma OT (g U:ℝ) (j k:ℕ) :
    f9 g U (j+k)=f9 g (aW g U j) k:=by
  unfold f9
  rw [P9]
lemma Ve (g U:ℝ) (j l r:ℕ) :
    List.ofFn (fun i:Fin (j+l+r)=>f9 g U i.val)=
      List.ofFn (fun i:Fin j=>f9 g U i.val)++
      List.ofFn (fun i:Fin l=>f9 g (aW g U j) i.val)++
      List.ofFn (fun i:Fin r=>f9 g (aW g U (j+l)) i.val):=by
  rw [List.ofFn_add,List.ofFn_add]
  simp only [Fin.val_castLE,Fin.val_natAdd,OT]
theorem SD {g U V:ℝ} {m:ℕ} (hg:0<g) (hg1:g<1)
    (hV:0<V) (hstart:V≤U) (RM:aW g U m≤V) :
    ∃ k,k ≤ m ∧ g^2*V<aW g U k ∧ aW g U k≤V:=by
  have hex:∃ k,aW g U k≤V:=⟨m,RM⟩
  let k:=Nat.find hex
  have hk:aW g U k≤V:=Nat.find_spec hex
  have hkm:k ≤ m:=Nat.find_min' hex RM
  refine ⟨k,hkm,?_,hk⟩
  by_cases hk0:k=0
  · simp only [hk0,aW,pow_zero,one_mul]
    have hg2:g^2<1:=pow_lt_one₀ hg.le hg1 (by omega:2≠0)
    exact (mul_lt_of_lt_one_left hV hg2).trans_le hstart
  · have hkpos:0<k:=Nat.pos_of_ne_zero hk0
    have W9:V<aW g U (k-1):=lt_of_not_ge (Nat.find_min hex (by omega))
    have he:k=k-1+1:=by omega
    rw [he,EU]
    exact mul_lt_mul_of_pos_left W9 (sq_pos_of_pos hg)
lemma Vm {g U:ℝ} (hg:0<g) (hU:0<U) (k:ℕ) :
    Real.log (aW g U k)=(k:ℝ)*(2*Real.log g)+Real.log U:=by
  unfold aW
  rw [Real.log_mul (ne_of_gt (pow_pos (sq_pos_of_pos hg) _)) hU.ne',Real.log_pow,Real.log_pow]
  norm_num
theorem Kz (ns:List ℕ) (N:ℕ) {H:ℝ} (hH:0≤H)
    (hns:∀ n∈ns,(n:ℝ)≤Real.exp H) :
    Real.log ((ns.sum+N:ℕ)+1)≤Real.log ((ns.length:ℝ)+1)+H+Real.log ((N:ℝ)+1):=by
  have hs:(ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp H:=by
    induction ns with
    | nil=>simp
    | cons n ns ih =>
      have hn:=hns n (List.mem_cons_self ..)
      have hi:=ih (fun m hm=>hns m (List.mem_cons_of_mem n hm))
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hn,hi]
  have he:1≤Real.exp H:=Real.one_le_exp_iff.mpr hH
  have hc:0≤(ns.length:ℝ)*Real.exp H:=mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hN:1≤(N:ℝ)+1:=by linarith only [(Nat.cast_nonneg N:(0:ℝ)≤N)]
  have hle:((ns.sum+N:ℕ)+1:ℝ)≤((ns.length:ℝ)+1)*Real.exp H*((N:ℝ)+1):=by
    simp only [Nat.cast_add]
    nlinarith only [hs,he,hc,hN,(Nat.cast_nonneg N:(0:ℝ)≤N)]
  have hh:=Real.log_le_log (show (0:ℝ)<((ns.sum+N:ℕ)+1) by positivity) hle
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_exp] at hh
  exact hh
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
structure g3 (D:ℝ) where
  schedule:List ℕ
  smoothing:ℕ
  batches:ℕ → ℕ
  last:ℕ
  lengths:ℕ → ℕ
  rates:ℕ → ℝ
  error:ℝ
  batch:∀ j≤last,kL D schedule smoothing (cP (batches j)) (lengths j)
    (c8 (gd (fun i=>cP (batches i)) j)) (rates j)
  divides:∀ j<last,lengths j∣lengths (j+1)
  nonneg:0≤error
  smooth:∀ j<last,∀ a<lengths (j+1),2*Real.binEntropy ((a:ℝ)/(smoothing+1))+
    ((a:ℝ)/(smoothing+1))*((lengths j:ℝ)*Real.log (bY D).card+
      2*c8 (gd (fun i=>cP (batches i)) (last+1)))≤error
  excess:Real.log (bY D).card+last*error<∑ j∈Finset.range (last+1),rates j
noncomputable def g3.primes {D:ℝ} (q:g3 D):Finset ℕ :=
  (Finset.range (q.last+1)).biUnion (fun j=>dS.d6 (q.batches j))
lemma g3.Rm {D:ℝ} (q:g3 D) :
    ∀ p∈q.primes,p.Prime ∧ p%4=1:=by
  intro p hp
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hp
  exact (dS.iw _ _ |>.mp hj).2.2
noncomputable def g3.sieve {D:ℝ} (q:g3 D):aE :=
  Kw q.primes q.Rm
lemma g3.OV {D:ℝ} (q:g3 D)
    {z:GaussianInt} (hz:z∈q.sieve.avoiding) {j:ℕ} (hj:j≤q.last) :
    z∈(cP (q.batches j)).avoiding:=by
  intro p hp
  exact hz p (Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (by omega),hp⟩)
theorem g3.sound {D:ℝ} (q:g3 D) (hD:1≤D) :
    ∀ z:ℕ → GaussianInt,(∀ t,z t∈q.sieve.avoiding) → Function.Injective z →
      (∀ t,dist (z (t+1):ℂ) (z t:ℂ)≤D) → False:=by
  intro z ha hz hs
  exact Ju hD q.schedule q.smoothing q.last
    (fun j=>cP (q.batches j)) q.lengths q.rates q.batch q.divides
    q.nonneg q.smooth q.excess z hz (fun _ hj t=>q.OV (ha t) hj)
    (fun t=>by simpa only [dist_comm] using hs t)
theorem wI
    (h:∀ D:ℝ,1≤D → Nonempty (g3 D)):kD:=by
  intro D hD
  obtain ⟨q⟩:=h D hD
  exact ⟨q.sieve,q.sound hD⟩
theorem Cn (s:aE) (pre post:List ℕ) (N l:ℕ)
    {D g U δ:ℝ} (hD:1≤D) (hg:0<g) (hg1:g≤1/200) (hU:0<U)
    (hL:1≤ s.aP)
    (hlog:2*(1+Real.log 18)≤g*aW g U l)
    (cQ:640*s.aP≤g^5*aW g U l)
    (hsize:Real.log 16+Real.log (max D ((bY (4*D)).card:ℝ))≤g^2*aW g U l)
    (sw:4*Real.log D+2*Real.log 36≤4*g*aW g U l)
    (sI:2*Real.log 16+4*Real.log D≤aW g U l/4)
    (hcap:⌊U/s.aP⌋₊≤ s.primes.card)
    (hpost:∀ n∈post,(n:ℝ)≤Real.exp (g*aW g U l))
    (hN:(N:ℝ)≤Real.exp (g*aW g U l))
    (hlen:(post.length+2:ℝ)≤Real.exp (g*aW g U l))
    (hconst:Real.log 36+2*Real.log D≤g*aW g U l)
    (hδ:(1/2:ℝ)^l+90*g≤δ) :
    Nonempty (fq s D
      (pre++List.ofFn (fun i:Fin l=>f9 g U i.val)++post)
      N (eD s g U l) δ):=by
  let V:=aW g U l
  have hV:0<V:=lU hg hU l
  have hLp:0<s.aP:=by linarith only [hL]
  have QI:g^5≤1:=pow_le_one₀ hg.le (by linarith only [hg1])
  have Wg:2*s.aP≤V:=by
    have hh:=mul_le_mul_of_nonneg_right QI hV.le
    change 640*s.aP≤g^5*V at cQ
    nlinarith only [cQ,hh,hLp]
  have hfloor:V/2≤(eD s g U l:ℝ)*s.aP:=by
    have hh:=Nat.lt_floor_add_one (V/s.aP)
    have hm:=mul_lt_mul_of_pos_right hh hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    change V/2≤(⌊V/s.aP⌋₊:ℝ)*s.aP
    linarith only [hm,Wg]
  have hshift:=Bh (fun _=>(0:GaussianInt)) post N hpost hN hlen
  simp only [jG,Nat.cast_add] at hshift
  rw [show 1+((post.sum:ℝ)+N)=(post.sum:ℝ)+N+1 by ring] at hshift
  have jz:Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤
      (10*g)*(eD s g U l:ℝ)*s.aP:=by
    rw [Real.log_mul (by linarith only [hD]:D≠0) (by positivity)]
    simp only [Nat.cast_add]
    have hc:Real.log 36+2*Real.log D≤g*V:=hconst
    have hm:=mul_le_mul_of_nonneg_left hfloor (show 0≤10*g by positivity)
    nlinarith only [hshift,hc,hm]
  exact ⟨⟨pre,post,g,U,l,10*g,rfl,rfl,hg,hg1,hU,hlog,cQ,hsize,sw,sI,
    hcap,jz,by linarith only [hδ]⟩⟩
lemma pQ {g U:ℝ} (hg:0≤g) (hg1:g≤1) (hU:0≤U) (j:ℕ) :
    (f9 g U j:ℝ)≤Real.exp (g*U):=by
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  have hh:=l7 hg hg1 hU (Nat.zero_le j)
  simpa only [aW,pow_zero,one_mul] using mul_le_mul_of_nonneg_left hh hg
lemma R8 {g U:ℝ} (hg:0≤g) (hg1:g≤1) (hU:0≤U)
    {i j:ℕ} (hij:i≤j) :
    (f9 g U j:ℝ)≤Real.exp (g*aW g U i):=by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (l7 hg hg1 hU hij) hg))
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
section
open scoped BigOperators Classical
noncomputable def g5 (D:ℝ):ℝ :=
  10000+100*|Real.log D|+100*|Real.log (max D ((bY (4*D)).card:ℝ))|
lemma qZ (D:ℝ):0<g5 D:=by
  unfold g5
  positivity
theorem pU (s:aE) (pre post:List ℕ) (N l:ℕ)
    {D g U δ:ℝ} (hD:1≤D) (hg:0<g) (hg1:g≤1/200) (hU:0<U)
    (hL:1≤ s.aP)
    (pL:g5 D*s.aP≤g^5*aW g U l)
    (hcap:⌊U/s.aP⌋₊≤ s.primes.card)
    (hpost:∀ n∈post,(n:ℝ)≤Real.exp (g*aW g U l))
    (hN:(N:ℝ)≤Real.exp (g*aW g U l))
    (hlen:(post.length+2:ℝ)≤Real.exp (g*aW g U l))
    (hδ:(1/2:ℝ)^l+90*g≤δ) :
    Nonempty (fq s D
      (pre++List.ofFn (fun i:Fin l=>f9 g U i.val)++post)
      N (eD s g U l) δ):=by
  let V:=aW g U l
  have hV:0<V:=lU hg hU l
  have hg01:g≤1:=by linarith only [hg1]
  have QI:g^5≤g:=by
    have hh:g^4≤1:=pow_le_one₀ hg.le hg01
    calc g^5=g^4*g:=by ring
         _ ≤ 1*g:=mul_le_mul_of_nonneg_right hh hg.le
         _ = g:=one_mul _
  have Yh:g^5≤g^2:=by
    have hh:g^3≤1:=pow_le_one₀ hg.le hg01
    calc g^5=g^3*g^2:=by ring
         _ ≤ 1*g^2:=mul_le_mul_of_nonneg_right hh (sq_nonneg _)
         _ = g^2:=one_mul _
  have hC:g5 D≤g^5*V:=by
    have hh:=mul_le_mul_of_nonneg_left hL (qZ D).le
    simp only [mul_one] at hh
    exact hh.trans pL
  have hCg:=hC.trans (mul_le_mul_of_nonneg_right QI hV.le)
  have Wh:=hC.trans (mul_le_mul_of_nonneg_right Yh hV.le)
  have XC:=hCg.trans (by nlinarith only [hg01,hV]:g*V≤V)
  have TD:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<16)
  have Yj:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<18)
  have Wi:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<36)
  have hld:=le_abs_self (Real.log D)
  have hla:=le_abs_self (Real.log (max D ((bY (4*D)).card:ℝ)))
  have ha:=abs_nonneg (Real.log D)
  have hb:=abs_nonneg (Real.log (max D ((bY (4*D)).card:ℝ)))
  have Xb:640≤g5 D:=by unfold g5; linarith only [ha,hb]
  apply Cn s pre post N l hD hg hg1 hU hL
  · dsimp only [g5] at hCg
    linarith only [hCg,Yj,ha,hb]
  · exact (mul_le_mul_of_nonneg_right Xb (by linarith only [hL])).trans pL
  · dsimp only [g5] at Wh
    linarith only [Wh,TD,hla,ha,hb]
  · dsimp only [g5] at hCg
    nlinarith only [hCg,Wi,hld,ha,hb]
  · dsimp only [g5] at XC
    linarith only [XC,TD,hld,ha,hb]
  · exact hcap
  · exact hpost
  · exact hN
  · exact hlen
  · dsimp only [g5] at hCg
    linarith only [hCg,Wi,hld,ha,hb]
  · exact hδ
open scoped BigOperators Classical
open Filter
theorem g9 (C:ℝ) {a:ℝ} (ha:0<a) (d:ℕ) :
    ∀ᶠ y:ℝ in atTop,C*y^d≤a*Real.exp y:=by
  by_cases hC:0<C
  · have hh:=(Real.isLittleO_pow_exp_atTop (n:=d)).bound (div_pos ha hC)
    filter_upwards [hh,eventually_ge_atTop (0:ℝ)] with y hy hy0
    rw [Real.norm_of_nonneg (pow_nonneg hy0 _),Real.norm_of_nonneg (Real.exp_nonneg _)] at hy
    have hm:=mul_le_mul_of_nonneg_left hy hC.le
    rwa [←mul_assoc,mul_div_cancel₀ _ hC.ne'] at hm
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (pow_nonneg hy _)).trans
      (mul_nonneg ha.le (Real.exp_nonneg _))
theorem nI (A B:ℝ) :
    ∀ᶠ y:ℝ in atTop,A*y+B≤y^2:=by
  filter_upwards [eventually_ge_atTop (max (|A|+|B|+1) 1)] with y hy
  have h1:1≤y:=(le_max_right _ _).trans hy
  have h2:|A|+|B|+1≤y:=(le_max_left _ _).trans hy
  have h3:A≤|A|:=le_abs_self _
  have h4:B≤|B|:=le_abs_self _
  nlinarith only [h1,h2,h3,h4,abs_nonneg A,abs_nonneg B]
noncomputable def dH (m:ℕ):ℝ:=Real.exp (-((m:ℝ)^2))
def dW (m:ℕ):ℕ:=4*m^2
lemma nT (m:ℕ):0<dH m:=Real.exp_pos _
lemma jM (m:ℕ):dH m≤1:=by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
lemma Bw (m:ℕ) :
    (1/2:ℝ)^(dW m)+90*dH m≤91*dH m:=by
  have hl:(1/2:ℝ)≤Real.log 2:=by
    have hh:=Real.one_sub_inv_le_log_of_pos (by norm_num:(0:ℝ)<2)
    norm_num at hh
    exact hh
  have he:(1/2:ℝ)^(dW m)≤dH m:=by
    rw [show (1/2:ℝ)=Real.exp (-Real.log 2) by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [dW,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [sq_nonneg (m:ℝ),hl]
  linarith only [he]
lemma KD (m:ℕ) (a:ℝ) :
    aW (dH m) (Real.exp (a*Real.exp m)) (dW m)=
      Real.exp (a*Real.exp m-8*(m:ℝ)^4):=by
  unfold aW dH dW
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  push_cast
  ring
theorem k5 {a:ℝ} (ha:0<a) (k:ℕ) :
    ∀ᶠ m:ℕ in atTop,
      Real.exp ((a/2)*Real.exp m)≤(dH m)^k *
        aW (dH m) (Real.exp (a*Real.exp m)) (dW m):=by
  have h4:=g9 8 (a:=a/4) (by positivity) 4
  have h2:=g9 (k:ℝ) (a:=a/4) (by positivity) 2
  have hh:=(h4.and h2).filter_mono (show Filter.map ((↑):ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ m:ℕ in atTop,_ at hh
  filter_upwards [hh] with m hm
  rw [KD]
  unfold dH
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hm.1,hm.2]
theorem zL (C:ℝ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ m:ℕ in atTop,91*dH m*(C*Real.exp m)≤ε:=by
  by_cases hC:0<C
  · have hh:=nI 1 (Real.log (91*C/ε))
    have hh':=hh.filter_mono (show Filter.map ((↑):ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
    filter_upwards [hh'] with m hm
    change 1*(m:ℝ)+Real.log (91*C/ε)≤(m:ℝ)^2 at hm
    have he:Real.exp ((m:ℝ)-(m:ℝ)^2)≤ε/(91*C):=by
      rw [←Real.exp_log (show 0<ε/(91*C) by positivity)]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div (by positivity) (by positivity)]
      rw [Real.log_div (by positivity) hε.ne'] at hm
      linarith only [hm]
    have hmul:=(le_div_iff₀ (show 0<91*C by positivity)).mp he
    unfold dH
    rw [show 91*Real.exp (-((m:ℝ)^2))*(C*Real.exp m)=
      Real.exp ((m:ℝ)-(m:ℝ)^2)*(91*C) by rw [Real.exp_sub,Real.exp_neg]; ring]
    exact hmul
  · filter_upwards [] with m
    have:C*Real.exp (m:ℝ)≤0:=mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (Real.exp_nonneg _)
    exact (mul_nonpos_of_nonneg_of_nonpos (by exact mul_nonneg (by norm_num) (nT m).le:0≤91*dH m) this).trans hε.le
end
section
open scoped BigOperators Classical
open Filter
lemma nJ {a:ℝ} (ha:0<a) (C:ℝ) :
    ∀ᶠ m:ℕ in atTop,C≤a*Real.exp m:=by
  have hh:Tendsto (fun m:ℕ=>Real.exp (m:ℝ)*a) atTop atTop :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const ha
  simpa only [mul_comm] using hh.eventually (eventually_ge_atTop C)
lemma i9 {a:ℝ} (ha:0<a) (C:ℝ) :
    ∀ᶠ m:ℕ in atTop,C*Real.exp m≤Real.exp (a*Real.exp m):=by
  have hh:=g9 (C/a) (a:=1) (by norm_num) 1
  have ht:Tendsto (fun m:ℕ=>a*Real.exp m) atTop atTop:=by
    simpa only [Function.comp_apply] using Filter.Tendsto.const_mul_atTop ha
      (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  filter_upwards [ht.eventually hh] with m hm
  simpa only [pow_one,one_mul,←mul_assoc,div_mul_cancel₀ _ ha.ne'] using hm
lemma zO {ε:ℝ} (hε:0<ε) :
    ∀ᶠ m:ℕ in atTop,dH m≤ε:=by
  have hh:=nI 0 (-Real.log ε)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh] with m hm
  change 0*(m:ℝ)-Real.log ε≤(m:ℝ)^2 at hm
  unfold dH
  rw [←Real.exp_log hε]
  apply Real.exp_le_exp.mpr
  linarith only [hm]
lemma Dl (s:aE) (hne:s.primes.Nonempty) {T δ U:ℝ}
    (hT:2≤T)
    (hp:∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hdense:δ*T/Real.log (2*T)≤ s.primes.card)
    (hsize:2*U≤δ*T):⌊U/s.aP⌋₊≤ s.primes.card:=by
  have hT0:0<T:=by linarith only [hT]
  have KR:0<Real.log T:=Real.log_pos (by linarith only [hT])
  have hm:=s.m5 hne hT0 hp
  have jE:0<s.aP:=KR.trans_le hm.1
  have hl2:Real.log 2≤Real.log T:=Real.log_le_log (by norm_num) hT
  have Xc:Real.log (2*T)≤2*s.aP:=by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith only [hl2,hm.1]
  have hlo:0<Real.log (2*T):=Real.log_pos (by linarith only [hT])
  have hd:δ*T≤(s.primes.card:ℝ)*Real.log (2*T):=(div_le_iff₀ hlo).mp hdense
  have hk:δ*T≤(s.primes.card:ℝ)*(2*s.aP):=hd.trans
    (mul_le_mul_of_nonneg_left Xc (Nat.cast_nonneg _))
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ jE).mpr
  nlinarith only [hsize,hk]
theorem oX {D A B a b δ:ℝ}
    (hD:1≤D) (hA:0<A) (ha:0<a) (haA:a<A)
    (hba:b≤a/2) (hδ:0<δ) :
    ∀ᶠ m:ℕ in atTop,∀ (s:aE) (T:ℝ) (pre post:List ℕ) (N:ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes,T≤(p:ℝ) ∧ (p:ℝ)≤2*T) →
      δ*T/Real.log (2*T)≤ s.primes.card →
      Real.exp (A*Real.exp m)≤T → Real.log T≤B*Real.exp m →
      (∀ n∈post,(n:ℝ)≤Real.exp (Real.exp (b*Real.exp m))) →
      (N:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      (post.length+2:ℝ)≤Real.exp (Real.exp (b*Real.exp m)) →
      Nonempty (fq s D
        (pre++List.ofFn (fun i:Fin (dW m) =>
          f9 (dH m) (Real.exp (a*Real.exp m)) i.val)++post)
        N (eD s (dH m) (Real.exp (a*Real.exp m)) (dW m))
        (91*dH m)):=by
  have cQ:=i9 (a:=a/2) (by positivity)
    (g5 D*(B+1))
  have jI:=nJ (a:=A-a) (by linarith only [haA]) (Real.log (2/δ))
  have htwo:=nJ hA 2
  filter_upwards [k5 ha 5,k5 ha 1,
    zO (show (0:ℝ)<1/200 by norm_num),cQ,jI,htwo]
    with m YZ hm1 jd cQ jI htwo
  intro s T pre post N hne hp hdense hT R9 hpost hN hlen
  have he1:1≤Real.exp (m:ℝ):=Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hT0:0<T:=(Real.exp_pos _).trans_le hT
  have hT2:2≤T:=by
    have hh:=Real.add_one_le_exp (A*Real.exp m)
    linarith only [hh,htwo,hT]
  have hm:=s.m5 hne hT0 hp
  have jE:1≤ s.aP:=by
    have hh:=Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at hh
    linarith only [hh,hm.1,htwo]
  have hl2:Real.log 2≤1:=by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    linarith only [hh]
  have Oa:s.aP≤(B+1)*Real.exp m:=by
    rw [Real.log_mul (by norm_num) hT0.ne'] at hm
    nlinarith only [hm.2,R9,hl2,he1]
  have pL:=(mul_le_mul_of_nonneg_left Oa (qZ D).le).trans
    (by simpa only [mul_assoc] using cQ.trans YZ)
  have hsize:2*Real.exp (a*Real.exp m)≤δ*T:=by
    have he:Real.exp (a*Real.exp m+Real.log (2/δ))≤Real.exp (A*Real.exp m):=by
      apply Real.exp_le_exp.mpr
      nlinarith only [jI]
    rw [Real.exp_add,Real.exp_log (div_pos (by norm_num) hδ)] at he
    have hh:=mul_le_mul_of_nonneg_left (he.trans hT) hδ.le
    have heq:δ*(Real.exp (a*Real.exp m)*(2/δ))=2*Real.exp (a*Real.exp m):=by field_simp
    rwa [heq] at hh
  have hcap:=Dl s hne hT2 hp hdense hsize
  have htail:Real.exp (b*Real.exp m)≤dH m*
      aW (dH m) (Real.exp (a*Real.exp m)) (dW m):=by
    simpa only [pow_one] using ((Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hba (Real.exp_nonneg _))).trans hm1)
  exact pU s pre post N (dW m) hD (nT m)
    jd (Real.exp_pos _) jE pL hcap
    (fun n hn=>(hpost n hn).trans (Real.exp_le_exp.mpr htail))
    (hN.trans (Real.exp_le_exp.mpr htail)) (hlen.trans (Real.exp_le_exp.mpr htail))
    (Bw m)
end
open scoped BigOperators Classical
lemma fq.M5 {s:aE} {D δ:ℝ} {ns:List ℕ} {N b:ℕ}
    (q:fq s D ns N b δ) (jE:0< s.aP):b≤ s.primes.card:=by
  rw [q.size]
  apply le_trans _ q.cap
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ jE.le
  have hh:=l7 q.positive.le (by linarith only [q.small]) q.scale.le (Nat.zero_le q.l)
  simpa only [aW,pow_zero,one_mul] using hh
lemma fq.Sb {s:aE} {D δ:ℝ} {ns:List ℕ} {N b:ℕ}
    (q:fq s D ns N b δ) (jE:0< s.aP) :
    aW q.g q.U q.l/2≤(b:ℝ)*s.aP:=by
  have hV:=lU q.positive q.scale q.l
  have QI:q.g^5≤1:=pow_le_one₀ q.positive.le (by linarith only [q.small])
  have hh:=mul_le_mul_of_nonneg_right QI hV.le
  have cQ:=q.large
  have Wg:2*s.aP≤aW q.g q.U q.l:=by nlinarith only [hh,cQ,jE]
  have hf:=Nat.lt_floor_add_one (aW q.g q.U q.l/s.aP)
  have hm:=mul_lt_mul_of_pos_right hf jE
  rw [div_mul_cancel₀ _ jE.ne',add_mul,one_mul] at hm
  have ht:aW q.g q.U q.l/2≤(⌊aW q.g q.U q.l/s.aP⌋₊:ℝ)*s.aP:=by
    linarith only [hm,Wg]
  simpa only [q.size,eD] using ht
lemma fq.size_pos {s:aE} {D δ:ℝ} {ns:List ℕ} {N b:ℕ}
    (q:fq s D ns N b δ) (jE:0< s.aP):0<b:=by
  have hh:=q.Sb jE
  have hV:=lU q.positive q.scale q.l
  by_contra h
  have hb:b=0:=by omega
  have he:(b:ℝ)=0:=by exact_mod_cast hb
  rw [he,zero_mul] at hh
  linarith only [hh,hV]
lemma Cr {s:aE} {g U C T:ℝ} {l:ℕ}
    (jE:0< s.aP) (hlog:0<Real.log T)
    (hm:s.aP≤2*Real.log T)
    (hV:2*s.aP≤aW g U l)
    (jR:C*T≤aW g U l) :
    C*T/(4*Real.log T)≤(eD s g U l:ℝ):=by
  have hf:=Nat.lt_floor_add_one (aW g U l/s.aP)
  have hh:=mul_lt_mul_of_pos_right hf jE
  rw [div_mul_cancel₀ _ jE.ne',add_mul,one_mul] at hh
  have hlo:aW g U l/2≤(eD s g U l:ℝ)*s.aP:=by
    change _≤(⌊aW g U l/s.aP⌋₊:ℝ)*_
    linarith only [hh,hV]
  have hu:=mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (eD s g U l))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hlo,hu,jR]
end GaussianMoat
end OAI
end
section
namespace OAI
universe c9
namespace GaussianMoat
section
open scoped BigOperators Classical
open Filter
noncomputable def c7:ℝ:=1/1000000
def e4:ℕ:=20
noncomputable def cZ (a:ℝ):ℝ:=(c7^2)^e4*a
lemma jg:0<c7:=by norm_num [c7]
lemma KG:c7≤1/200:=by norm_num [c7]
lemma jZ {a:ℝ} (ha:0<a):0<cZ a:=by
  unfold cZ; exact mul_pos (pow_pos (sq_pos_of_pos jg) _) ha
lemma Ro:(1/2:ℝ)^e4+90*c7≤1/10000:=by
  norm_num [c7,e4]
theorem Jv {D a δ:ℝ} (hD:1≤D) (ha:0<a)
    (KI:2*a≤δ) :
    ∀ᶠ x:ℝ in atTop,∀ (s:aE) (pre post:List ℕ),
      s.primes.Nonempty →
      (∀ p∈s.primes,Real.exp x≤(p:ℝ) ∧ (p:ℝ)≤2*Real.exp x) →
      δ*Real.exp x/Real.log (2*Real.exp x)≤ s.primes.card →
      (∀ n∈post,(n:ℝ)≤Real.exp (c7*cZ a*Real.exp x)) →
      (post.length+2:ℝ)≤Real.exp (c7*cZ a*Real.exp x) →
      Nonempty (fq s D
        (pre++List.ofFn (fun i:Fin e4 =>
          f9 c7 (a*Real.exp x) i.val)++post)
        0 (eD s c7 (a*Real.exp x) e4) (1/10000)) ∧
      cZ a*Real.exp x/(4*x)≤
        (eD s c7 (a*Real.exp x) e4:ℝ):=by
  have hc:=jZ ha
  have cQ:=g9 (2*g5 D)
    (a:=c7^5*cZ a) (mul_pos (pow_pos jg _) hc) 1
  filter_upwards [cQ,eventually_ge_atTop (2:ℝ)] with x cQ hx
  intro s pre post hne hp hdense hpost hlen
  have hT2:2≤Real.exp x:=by linarith only [Real.add_one_le_exp x,hx]
  have hm:=s.m5 hne (Real.exp_pos x) hp
  rw [Real.log_exp] at hm
  have jE:1≤ s.aP:=by linarith only [hm.1,hx]
  have S8:0< s.aP:=by linarith only [jE]
  have vG:Real.log 2≤x:=by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    linarith only [hh,hx]
  have Oa:s.aP≤2*x:=by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hm
    linarith only [hm.2,vG]
  have jR:aW c7 (a*Real.exp x) e4=cZ a*Real.exp x:=by
    unfold aW cZ; ring
  have pL:g5 D*s.aP≤c7^5*
      aW c7 (a*Real.exp x) e4:=by
    have hh:=mul_le_mul_of_nonneg_left Oa (qZ D).le
    rw [jR]
    simp only [pow_one] at cQ
    nlinarith only [hh,cQ]
  have hcap:=Dl s hne hT2 hp hdense
    (by nlinarith only [KI,Real.exp_pos x]:2*(a*Real.exp x)≤δ*Real.exp x)
  have Ob:=pU s pre post 0 e4 hD jg
    KG (mul_pos ha (Real.exp_pos _)) jE pL hcap
    (by simpa only [jR,mul_assoc] using hpost)
    (by simp only [Nat.cast_zero]; positivity)
    (by simpa only [jR,mul_assoc] using hlen) Ro
  refine ⟨Ob,?_⟩
  have QI:c7^5≤1:=pow_le_one₀ jg.le (by norm_num [c7])
  have Xd:=lU jg (mul_pos ha (Real.exp_pos x)) e4
  have hn:=mul_le_mul_of_nonneg_right QI Xd.le
  have hC:2≤g5 D:=by
    unfold g5
    linarith only [abs_nonneg (Real.log D),abs_nonneg (Real.log (max D ((bY (4*D)).card:ℝ)))]
  have hm2:=mul_le_mul_of_nonneg_right hC S8.le
  have hV:2*s.aP≤aW c7 (a*Real.exp x) e4:=by
    nlinarith only [pL,hn,hm2]
  have hh:=Cr S8
    (show 0<Real.log (Real.exp x) by rw [Real.log_exp]; linarith only [hx])
    (by simpa only [Real.log_exp] using Oa) hV (le_of_eq jR.symm)
  simpa only [Real.log_exp] using hh
end
open scoped BigOperators Classical
noncomputable def mo (a:ℝ) (j:ℕ):List ℕ :=
  List.ofFn (fun i:Fin e4=>f9 c7 (a*(2:ℝ)^j) i.val)
noncomputable def j3 (a:ℝ) (J:Finset ℕ):List ℕ :=
  (J.sort (·≥·)).flatMap (mo a)
noncomputable def dL (m:ℕ) (a:ℝ):List ℕ :=
  List.ofFn (fun i:Fin (dW m) =>
    f9 (dH m) (Real.exp (a*Real.exp m)) i.val)
lemma Bz (a:ℝ) (J:Finset ℕ) :
    (j3 a J).length=J.card*e4:=by
  unfold j3
  rw [List.length_flatMap]
  simp only [mo,List.length_ofFn,List.map_const',List.sum_replicate,Finset.length_sort,
    smul_eq_mul]
lemma Fj {a H:ℝ} (ha:0≤a) (j:ℕ)
    (h:c7*a*(2:ℝ)^j≤H) :
    ∀ n∈mo a j,(n:ℝ)≤Real.exp H:=by
  intro n hn
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hn
  exact (pQ jg.le
    (by norm_num [c7]) (mul_nonneg ha (by positivity)) i.val).trans
    (Real.exp_le_exp.mpr (by simpa only [mul_assoc] using h))
lemma n8 {a H:ℝ} {m:ℕ} (hg:dH m≤1)
    (h:dH m*Real.exp (a*Real.exp m)≤H) :
    ∀ n∈dL m a,(n:ℝ)≤Real.exp H:=by
  intro n hn
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hn
  exact (pQ (nT m).le hg (Real.exp_nonneg _) i.val).trans
    (Real.exp_le_exp.mpr h)
lemma QJ {J:Finset ℕ} {j:ℕ} (hj:j∈J) :
    ∃ pre post:List ℕ,J.sort (·≥·)=pre++j::post ∧
      (∀ i∈post,i∈J ∧ i < j) ∧ (∀ i∈pre,i∈J ∧ j < i):=by
  have hm:j∈J.sort (·≥·):=(Finset.mem_sort (·≥·)).mpr hj
  obtain ⟨pre,post,he⟩:=List.mem_iff_append.mp hm
  have hp:(J.sort (·≥·)).Pairwise (·>·):=by
    exact (Finset.sortedGT_sort J).pairwise
  rw [he,List.pairwise_append,List.pairwise_cons] at hp
  refine ⟨pre,post,he,?_,?_⟩
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.1.1 i hi⟩
    rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hi)
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.2 i hi j (List.mem_cons_self ..)⟩
    rw [he]; exact List.mem_append_left _ hi
lemma Oc {a:ℝ} {J:Finset ℕ} {j:ℕ} (hj:j∈J) :
    ∃ pre post:List ℕ,j3 a J=pre++mo a j++post ∧
      post.length≤J.card*e4 ∧
      (∀ n∈post,∃ i∈J,i<j ∧ n∈mo a i):=by
  obtain ⟨A,B,he,hB,_⟩:=QJ hj
  refine ⟨A.flatMap (mo a),B.flatMap (mo a),?_,?_,?_⟩
  · simp only [j3,he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  · have hh:(B.flatMap (mo a)).length≤(j3 a J).length:=by
      simp only [j3,he,List.flatMap_append,List.flatMap_cons,List.length_append]
      omega
    simpa only [Bz] using hh
  · intro n hn
    obtain ⟨i,hi,hn⟩:=List.mem_flatMap.mp hn
    exact ⟨i,(hB i hi).1,(hB i hi).2,hn⟩
noncomputable def gJ (a:ℝ) (m:ℕ) (J:ℕ → Finset ℕ) (W:ℕ):List ℕ :=
  ((List.range W).reverse).flatMap (fun w =>
    j3 a (J w)++dL m ((100:ℝ)^w/4))
lemma yQ (a:ℝ) (m:ℕ) (J:ℕ → Finset ℕ) (W:ℕ) :
    gJ a m J (W+1)=j3 a (J W)++dL m ((100:ℝ)^W/4)++
      gJ a m J W:=by
  simp only [gJ,List.range_succ,List.reverse_append,List.reverse_singleton,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
lemma oY (a:ℝ) (m:ℕ) (J:ℕ → Finset ℕ) {W w:ℕ} (hw:w<W) :
    ∃ pre,gJ a m J W=pre++j3 a (J w)++
      dL m ((100:ℝ)^w/4)++gJ a m J w:=by
  induction W with
  | zero=>omega
  | succ W ih =>
    rw [yQ]
    by_cases he:w=W
    · subst w; exact ⟨[],by simp only [List.nil_append]⟩
    · obtain ⟨pre,hp⟩:=ih (by omega)
      rw [hp]
      exact ⟨j3 a (J W)++dL m ((100:ℝ)^W/4)++pre,by simp only [List.append_assoc]⟩
lemma M6 (a:ℝ) (m:ℕ) (J:ℕ → Finset ℕ) {W n:ℕ}
    (hn:n∈gJ a m J W) :
    ∃ w<W,n∈j3 a (J w) ∨ n∈dL m ((100:ℝ)^w/4):=by
  obtain ⟨w,hw,hn⟩:=List.mem_flatMap.mp hn
  exact ⟨w,List.mem_range.mp (List.mem_reverse.mp hw),List.mem_append.mp hn⟩
theorem Jw (J:Finset ℕ) {K j:ℕ} (hK:0<K)
    (hsep:∀ a∈J,∀ b∈J,a<b → a+K≤b)
    (hcap:∀ a∈J,a+K≤j) :
    (∑ a∈J,(2:ℝ)^a)≤(2:ℝ)^j/((2:ℝ)^K-1):=by
  have hden:0<(2:ℝ)^K-1:=by
    have hh:=one_lt_pow₀ (by norm_num:(1:ℝ)<2) (by omega:K≠0)
    linarith only [hh]
  induction J using Finset.induction_on_max generalizing j with
  | empty=>simp only [Finset.sum_empty]; positivity
  | @insert a J hmax ih =>
    have ha:a∉J:=fun h=>(lt_irrefl a) (hmax a h)
    have hci:∀ b∈J,b+K≤a:=by
      intro b hb
      exact hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self ..)
        (hmax b hb)
    have hi:=ih (fun b hb c hc hbc=>hsep b (Finset.mem_insert_of_mem hb)
      c (Finset.mem_insert_of_mem hc) hbc) hci
    rw [Finset.sum_insert ha]
    have hp:=pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) (hcap a (Finset.mem_insert_self ..))
    have hd:=(div_le_div_iff_of_pos_right hden).mpr hp
    rw [pow_add] at hd
    have he:(2:ℝ)^a+(2:ℝ)^a/((2:ℝ)^K-1)=(2:ℝ)^a*2^K/(2^K-1):=by
      field_simp; ring
    exact (add_le_add (le_refl ((2:ℝ)^a)) hi).trans (he ▸ hd)
lemma D8 (F G:Finset GaussianInt) :
    c8 (F∪G)≤c8 F+c8 G:=by
  classical
  have hh:=Finset.sum_union_inter (s₁:=F) (s₂:=G) (f:=fun f:GaussianInt=>Real.log f.norm.natAbs)
  change c8 (F∪G)+c8 (F∩G)=c8 F+c8 G at hh
  linarith only [hh,G7 (F∩G)]
lemma oZ {ι:Type c9} (J:Finset ι) (F:ι → Finset GaussianInt) :
    c8 (J.biUnion F)≤∑ j∈J,c8 (F j):=by
  induction J using Finset.induction_on with
  | empty=>simp [c8]
  | @insert j J hj ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert hj]
    exact (D8 _ _).trans (add_le_add (le_refl _) ih)
lemma Fk (J:Finset ℕ) {K j:ℕ} (hK:0<K)
    (hsep:∀ a∈J,∀ b∈J,a<b → a+K≤b)
    (hcap:∀ a∈J,a+K≤j) :
    c8 (J.biUnion (fun a=>(cP a).e6))≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^j:=by
  have hsum:=Finset.sum_le_sum (fun a (_:a∈J)=>nC a)
  rw [←Finset.mul_sum] at hsum
  have hh:=mul_le_mul_of_nonneg_left (Jw J hK hsep hcap)
    (show 0≤4*Real.log 4 by positivity)
  have ht:=(oZ J (fun a=>(cP a).e6)).trans (hsum.trans hh)
  calc
    _ ≤ 4*Real.log 4*((2:ℝ)^j/(2^K-1)):=ht
    _ = _:=by ring
open scoped BigOperators Classical
open Filter
lemma Qa:(1/2:ℝ)≤Real.log 2:=by
  have hh:=Real.one_sub_inv_le_log_of_pos (by norm_num:(0:ℝ)<2)
  norm_num at hh
  exact hh
lemma q5 {X:ℝ} (hX:2≤X) (J:Finset ℕ)
    (hJ:∀ j∈J,(j:ℝ)*Real.log 2≤21/20*X) :
    (J.card:ℝ)≤3*X:=by
  have hj:∀ j∈J,(j:ℝ)≤21/10*X:=by
    intro j hj
    have hh:=mul_le_mul_of_nonneg_left Qa (Nat.cast_nonneg j)
    linarith only [hh,hJ j hj]
  have hs:J⊆Finset.range (⌊21/10*X⌋₊+1):=by
    intro j hj'
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr (hj j hj'))
  have hc:(J.card:ℝ)≤(⌊21/10*X⌋₊:ℝ)+1:=by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hf:=Nat.floor_le (show 0≤21/10*X by linarith only [hX])
  linarith only [hc,hf,hX]
lemma KO {a:ℝ} (ha:0<a) {i j K:ℕ}
    (jI:a≤(2:ℝ)^K*cZ a) (hij:i+K≤j) :
    ∀ n∈mo a i,(n:ℝ)≤Real.exp (c7*cZ a*(2:ℝ)^j):=by
  apply Fj ha.le
  have hh:=mul_le_mul_of_nonneg_left jI (show 0≤(2:ℝ)^i by positivity)
  rw [←mul_assoc,←pow_add] at hh
  have hp:(2:ℝ)^(i+K)≤(2:ℝ)^j:=pow_le_pow_right₀ (by norm_num) hij
  have hp':=mul_le_mul_of_nonneg_right hp (jZ ha).le
  have hg:=mul_le_mul_of_nonneg_left (hh.trans hp') jg.le
  nlinarith only [hg]
theorem Fo {D a δ:ℝ} {K:ℕ}
    (hD:1≤D) (ha:0<a) (KI:2*a≤δ)
    (jI:a≤(2:ℝ)^K*cZ a) :
    ∀ᶠ X:ℝ in atTop,∀ (J:Finset ℕ) (initial:List ℕ),
      (∀ i∈J,∀ j∈J,i<j → i+K≤j) →
      (∀ j∈J,X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card) →
      ∀ j∈J,Nonempty (fq (cP j) D (initial++j3 a J)
        0 (eD (cP j) c7 (a*(2:ℝ)^j) e4) (1/10000)) ∧
        cZ a*(2:ℝ)^j/(4*Real.log ((2:ℝ)^j))≤
          (eD (cP j) c7 (a*(2:ℝ)^j) e4:ℝ):=by
  have hδ:0<δ:=by linarith only [ha,KI]
  have htop:=Jv hD ha KI
  have hlen:=g9 (100:ℝ)
    (a:=c7*cZ a) (mul_pos jg (jZ ha)) 1
  obtain ⟨x0,h0⟩:=eventually_atTop.mp (htop.and hlen)
  filter_upwards [eventually_ge_atTop (max x0 2)] with X hX
  intro J initial hsep hJ j hj
  have hX2:2≤X:=(le_max_right _ _).trans hX
  have hX0:x0≤X:=(le_max_left _ _).trans hX
  have hlog:=(hJ j hj).1
  have UK:=(hJ j hj).2.1
  obtain ⟨Ob,hlen⟩:=h0 (j*Real.log 2) (hX0.trans hlog)
  have hn:(cP j).primes.Nonempty:=by
    apply Finset.card_pos.mp
    have Xf:0<Real.log ((2:ℝ)^(j+1)):=by
      rw [Real.log_pow]
      positivity
    have hh:=(hJ j hj).2.2
    have hp:0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)):=div_pos (by positivity) Xf
    have hc:(0:ℝ)<(dS.d6 j).card:=hp.trans_le hh
    exact_mod_cast hc
  obtain ⟨pre,post,he,hpl,hpm⟩:=Oc (a:=a) hj
  have hT:Real.exp (j*Real.log 2)=(2:ℝ)^j:=by rw [Real.exp_nat_mul,Real.exp_log (by norm_num:(0:ℝ)<2)]
  have hcard:=q5 hX2 J (fun i hi=>(hJ i hi).2.1)
  have hlen':(post.length+2:ℝ)≤Real.exp (c7*cZ a*(2:ℝ)^j):=by
    have hp:(post.length:ℝ)≤(J.card:ℝ)*e4:=by exact_mod_cast hpl
    simp only [pow_one,hT] at hlen
    have he:=Real.add_one_le_exp (c7*cZ a*(2:ℝ)^j)
    norm_num only [e4,Nat.cast_ofNat] at hp
    nlinarith only [hp,hcard,hlen,he,hlog,hX2]
  have hprime:∀ p∈(cP j).primes,Real.exp (j*Real.log 2)≤(p:ℝ) ∧
      (p:ℝ)≤2*Real.exp (j*Real.log 2):=by
    intro p hp
    rw [hT]
    have hh:=(dS.iw j p).mp hp
    constructor
    · exact_mod_cast hh.1
    · have hh':p≤2^(j+1):=hh.2.1.le
      rw [pow_succ] at hh'
      exact_mod_cast (by simpa only [mul_comm] using hh':p≤2*2^j)
  have hdense:δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (cP j).primes.card:=by
    change δ*Real.exp (j*Real.log 2)/Real.log (2*Real.exp (j*Real.log 2))≤
      (dS.d6 j).card
    simpa only [hT,pow_succ,mul_comm] using (hJ j hj).2.2
  have Yk:∀ n∈post,(n:ℝ)≤Real.exp (c7*cZ a*Real.exp (j*Real.log 2)):=by
    intro n hnp
    obtain ⟨i,hi,hij,hni⟩:=hpm n hnp
    rw [hT]
    exact KO ha jI (hsep i hi j hj hij) n hni
  obtain ⟨hb,QN⟩:=Ob (cP j) (initial++pre) post hn hprime hdense Yk
    (by simpa only [hT] using hlen')
  refine ⟨?_,?_⟩
  · simpa only [hT,he,mo,List.append_assoc] using hb
  · simpa only [hT,Real.log_pow] using QN
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
theorem Ly (s:aE) (D:ℝ) (N:ℕ)
    (mid bot:List ℕ) (b q n:ℕ) (e Sd:ℝ)
    (u:s.bZ → ℝ)
    (hm:fq s D mid 0 b e)
    (hb:fq s D bot N q Sd)
    (hb0:0<b) (hbk:b≤ s.primes.card) (hq0:0<q) (hqk:q≤ s.primes.card)
    (hN:1≤bot.sum+N) (hn:0<n)
    (hprime:∀ i,Real.exp 100≤(s.bD i:ℝ))
    (hu:∀ i,0<u i)
    (hbase:Sd*s.aP≤Real.exp (-100)/(512*640000))
    (jI:e*s.aP+n*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b<1/256)
    (iJ:∀ i,(s.bD i:ℝ)*Real.exp
      (-(n:ℝ)*(1/64)^2*u i/(2*(s.bD i:ℝ)))≤1/640000) :
    gG s D N (mid++bot) (1/4) u (1/100):=by
  let c:ℝ:=Real.exp (-100)/512
  let u':s.bZ → ℝ:=fun i=>Real.exp (-100)/64*(s.bD i:ℝ)
  let C:s.bZ → ℝ:=fun i=>Real.exp (-100)*(s.bD i:ℝ)
  have hc:0<c:=by dsimp [c]; positivity
  have htail:gG s D N bot (1/4+4*(1/64)) u' (1/640000):=by
    apply gG.base bot q (1/4+4*(1/64)) c Sd (1/640000) u' hb hq0 hqk
    · norm_num
    · exact hc
    · intro i; dsimp [c,u']; ring_nf; exact le_rfl
    · apply (div_le_iff₀ hc).mpr
      dsimp [c]
      linarith only [hbase]
  apply gG.step mid bot b n (1/4) (1/64) (1/640000) (1/100)
    (1/640000) e 100 u u' C hm htail hN hn hb0 hbk
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hu
  · norm_num
  · norm_num only [mul_one,one_mul,div_div]
    have hl2:Real.log 2≤1:=by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    have hl:Real.log (12800:ℝ)≤14:=by
      have hh:=Real.log_le_log (by norm_num:(0:ℝ)<12800) (by norm_num:(12800:ℝ)≤2^14)
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith only [hh,hl2]
    rw [show (1:ℝ)/12800=(12800:ℝ)⁻¹ by rw [one_div],Real.log_inv]
    linarith only [hl]
  · norm_num only [Nat.cast_ofNat] at jI ⊢
    convert jI using 1
  · intro i
    have hh:=mul_le_mul_of_nonneg_left (hprime i) (Real.exp_nonneg (-100))
    dsimp [C]
    rw [←Real.exp_add] at hh
    norm_num at hh
    exact hh
  · intro i
    dsimp [C]
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt ((Real.exp_pos 100).trans_le (hprime i))),Real.log_exp]
    linarith
  · intro i; dsimp [u',C]; ring_nf; exact le_rfl
  · exact iJ
lemma Cu {X T p L n:ℝ} (hX:1600≤X)
    (hT:Real.exp X≤T) (hp0:0<p) (hp:p≤2*T)
    (hn:256*T*Real.log (2*T)≤n*L) :
    Real.log (4*(p*Real.exp (-X/200))+p*Real.exp (-(n:ℝ)*(L*((1/4)/p)/2)/4))≤
      Real.log p-X/400:=by
  have hX0:0≤X:=by linarith only [hX]
  have hT0:0<T:=(Real.exp_pos X).trans_le hT
  have hlog:X≤Real.log T:=by
    exact (Real.log_exp X).symm ▸ Real.log_le_log (Real.exp_pos X) hT
  have vG:X≤Real.log (2*T):=hlog.trans (Real.log_le_log hT0 (by linarith only [hT0]))
  have Y0:Real.log 8≤3:=by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num at hh ⊢
    linarith only [hh]
  have Xg:4*Real.exp (-X/200)≤Real.exp (-X/400)/2:=by
    have he : -X/200≤-X/400-Real.log 8:=by linarith only [hX,Y0]
    have hh:=Real.exp_le_exp.mpr he
    rw [Real.exp_sub,Real.exp_log (by norm_num:(0:ℝ)<8)] at hh
    linarith only [hh]
  have cQ:4*Real.log (2*T)≤n*L/(32*p):=by
    apply (le_div_iff₀ (by positivity)).mpr
    have hp':=mul_le_mul_of_nonneg_right hp (show 0≤128*Real.log (2*T) by linarith only [vG,hX0])
    nlinarith only [hn,hp']
  have jd:Real.exp (-n*(L*((1/4)/p)/2)/4)≤Real.exp (-X/400)/2:=by
    have hl2:Real.log 2≤1:=by
      have hh:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
      linarith only [hh]
    have he : -n*(L*((1/4)/p)/2)/4≤-X/400-Real.log 2:=by
      have heq : -n*(L*((1/4)/p)/2)/4= -(n*L/(32*p)):=by ring
      rw [heq]
      linarith only [cQ,vG,hX,hl2]
    have hh:=Real.exp_le_exp.mpr he
    rwa [Real.exp_sub,Real.exp_log (by norm_num:(0:ℝ)<2)] at hh
  have harg:4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)≤
      p*Real.exp (-X/400):=by
    have h1:=mul_le_mul_of_nonneg_left Xg hp0.le
    have h2:=mul_le_mul_of_nonneg_left jd hp0.le
    nlinarith only [h1,h2]
  have hh:=Real.log_le_log (by positivity:0<4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)) harg
  rw [Real.log_mul hp0.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith only [hh]
lemma Cv {X T L n b H E c mean:ℝ}
    (hX:1≤X) (hT:0<T) (hc:0<c)
    (hlog:X≤Real.log T) (UK:Real.log T≤21/20*X)
    (jE:mean≤2*X) (hb:c*T/Real.log T≤b)
    (hn:n*L≤1024*T*Real.log T)
    (hshift:2*n*H≤c*T/5000) (hE:E≤c*T/10000) :
    n*(L*(c/(10000000*Real.log T))+2*H)≤
      b*((X/400)*(1-2*(1/100))-(1/10000)*mean)-E:=by
  have UN:0<Real.log T:=by linarith only [hX,hlog]
  have hb0:0<b:=(div_pos (mul_pos hc hT) UN).trans_le hb
  have hbg:c*T≤b*Real.log T:=(div_le_iff₀ UN).mp hb
  have Yl:c*T≤b*(21/20*X):=hbg.trans (mul_le_mul_of_nonneg_left UK hb0.le)
  have Xh:X/500≤(X/400)*(1-2*(1/100))-(1/10000)*mean:=by
    nlinarith only [jE,hX]
  have hrev:=mul_le_mul_of_nonneg_left Xh hb0.le
  have jz:=mul_le_mul_of_nonneg_right hn (show 0≤c/(10000000*Real.log T) by positivity)
  have heq:(1024*T*Real.log T)*(c/(10000000*Real.log T))=1024*c*T/10000000:=by
    field_simp
  rw [heq] at jz
  nlinarith only [Yl,hrev,jz,hshift,hE,mul_pos hc hT]
open scoped BigOperators Classical
open Filter
lemma fD (C:ℝ) {a:ℝ} (ha:0<a) (d:ℕ) :
    ∀ᶠ X:ℝ in atTop,C*X^d≤Real.exp (a*X):=by
  have h:=g9 (C/a^d) (a:=1) (by norm_num) d
  have ht:Tendsto (fun x:ℝ=>a*x) atTop atTop:=tendsto_id.const_mul_atTop ha
  filter_upwards [ht.eventually h] with X hX
  simp only [one_mul,mul_pow] at hX
  convert hX using 1; field_simp
lemma j4 {a b:ℝ} (hab:a<b) (C:ℝ) :
    ∀ᶠ X:ℝ in atTop,C*Real.exp (a*X)≤Real.exp (b*X):=by
  have h:=fD C (sub_pos.mpr hab) 0
  filter_upwards [h] with X hX
  simp only [pow_zero,mul_one] at hX
  have hh:=mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (a*X))
  rw [←Real.exp_add] at hh
  convert hh using 1
  congr 1
  ring_nf
noncomputable def cE (j:ℕ):ℕ:=2^(2*j/5)
noncomputable def gI (j:ℕ):ℕ :=
  ⌈256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/cE j⌉₊
lemma uj (j:ℕ):0<cE j:=by
  unfold cE; positivity
lemma Jx {i j:ℕ} (hij:i≤j):cE i∣cE j:=by
  exact pow_dvd_pow 2 (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hij))
lemma Jy (j:ℕ) :
    (2/5:ℝ)*(j*Real.log 2)-Real.log 2≤Real.log (cE j:ℝ) ∧
    Real.log (cE j:ℝ)≤(2/5:ℝ)*(j*Real.log 2):=by
  have hp:0<Real.log (2:ℝ):=Real.log_pos (by norm_num)
  have h1:5*(2*j/5)≤2*j:=Nat.mul_div_le _ _
  have h2:2*j<5*(2*j/5+1):=Nat.lt_mul_div_succ _ (by norm_num)
  have h1':5*(2*j/5:ℕ)≤(2:ℝ)*j:=by exact_mod_cast h1
  have h2':(2:ℝ)*j<5*((2*j/5:ℕ)+1):=by exact_mod_cast h2
  have hh1:=mul_le_mul_of_nonneg_right h1' hp.le
  have hh2:=mul_lt_mul_of_pos_right h2' hp
  simp only [cE,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  constructor <;> nlinarith only [hh1,hh2]
lemma o7 (j:ℕ):(cE j:ℝ)≤(2:ℝ)^j:=by
  unfold cE
  push_cast
  apply pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2)
  omega
theorem rJ {D:ℝ} (hD:1≤D) :
    ∀ᶠ X:ℝ in atTop,∀ j:ℕ,
      X≤j*Real.log 2 → j*Real.log 2≤21/20*X →
      0<gI j ∧
      (D*(cE j:ℝ))^2<(2:ℝ)^j ∧
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
        (gI j:ℝ)*cE j ∧
      (gI j:ℝ)*cE j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) ∧
      (gI j:ℝ)≤Real.exp (7/10*X) ∧
      (cE j:ℝ)≤Real.exp (21/50*X):=by
  have oA:=fD (1024:ℝ) (a:=1/100) (by norm_num) 1
  have KV:=j4 (a:=0) (b:=4/25) (by norm_num) (2*D^2)
  filter_upwards [oA,KV,eventually_ge_atTop (100:ℝ)] with X oA KV hX
  intro j hlo hhi
  have hl2:Real.log (2:ℝ)≤1:=by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    linarith only [hh]
  have hT:Real.log ((2:ℝ)^j)=(j:ℝ)*Real.log 2:=Real.log_pow _ _
  have o9:0<(2:ℝ)^j:=by positivity
  have H7:0<(cE j:ℝ):=by exact_mod_cast uj j
  have UO:=Jy j
  have Ym:Real.exp (39/100*X)≤(cE j:ℝ):=by
    rw [←Real.exp_log H7]
    apply Real.exp_le_exp.mpr
    nlinarith only [UO.1,hlo,hl2,hX]
  have TY:(cE j:ℝ)≤Real.exp (21/50*X):=by
    rw [←Real.exp_log H7]
    apply Real.exp_le_exp.mpr
    nlinarith only [UO.2,hhi]
  have Zp:(2:ℝ)^j≤Real.exp (21/20*X):=by
    rw [←Real.exp_log o9,hT]
    exact Real.exp_le_exp.mpr hhi
  have Yn:Real.exp X≤(2:ℝ)^j:=by
    rw [←Real.exp_log o9,hT]
    exact Real.exp_le_exp.mpr hlo
  have KR:1≤Real.log ((2:ℝ)^j):=by rw [hT]; linarith only [hlo,hX]
  have Qn:Real.log (2*(2:ℝ)^j)=Real.log 2+Real.log ((2:ℝ)^j) :=
    Real.log_mul (by norm_num) o9.ne'
  have hnum:0<256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j):=by
    rw [Qn]; positivity
  have RY:256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
      (gI j:ℝ)*cE j:=by
    exact (div_le_iff₀ H7).mp (Nat.le_ceil _)
  have Mz:(gI j:ℝ)*cE j≤
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)+(cE j:ℝ):=by
    have hh:=(Nat.ceil_lt_add_one (show 0≤256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/cE j by positivity)).le
    have hm:=mul_le_mul_of_nonneg_right hh H7.le
    rw [add_mul,one_mul,div_mul_cancel₀ _ H7.ne'] at hm
    exact hm
  have hprod:(gI j:ℝ)*cE j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j):=by
    have hL:=o7 j
    rw [Qn] at Mz
    have hh:=mul_le_mul_of_nonneg_left hl2 (show 0≤256*(2:ℝ)^j by positivity)
    have hh':=mul_le_mul_of_nonneg_left KR (show 0≤(2:ℝ)^j by positivity)
    nlinarith only [Mz,hL,hh,hh',o9]
  have Vf:(gI j:ℝ)≤Real.exp (7/10*X):=by
    have Wj:(gI j:ℝ)*(cE j:ℝ)≤
        1024*Real.exp (21/20*X)*(21/20*X):=by
      apply hprod.trans
      gcongr
      rw [hT]; exact hhi
    have hn':=mul_le_mul_of_nonneg_left Ym (Nat.cast_nonneg (gI j))
    have hc:1024*(21/20*X)≤Real.exp (4/100*X):=by
      have he:=Real.add_one_le_exp (3/100*X)
      have he':(21/20:ℝ)≤Real.exp (3/100*X):=by linarith only [he,hX]
      have hm:=mul_le_mul oA he' (by norm_num) (Real.exp_nonneg _)
      simp only [pow_one] at hm
      rw [←Real.exp_add] at hm
      rw [show 1/100*X+3/100*X=4/100*X by ring] at hm
      linarith only [hm]
    have hh:=mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (21/20*X))
    rw [←Real.exp_add] at hh
    have hlast:(gI j:ℝ)*Real.exp (39/100*X)≤
        Real.exp (7/10*X)*Real.exp (39/100*X):=by
      apply hn'.trans (Wj.trans _)
      rw [←Real.exp_add]
      rw [show 4/100*X+21/20*X=7/10*X+39/100*X by ring] at hh
      nlinarith only [hh]
    nlinarith only [hlast,Real.exp_pos (39/100*X)]
  refine ⟨?_,?_,RY,hprod,Vf,TY⟩
  · exact Nat.ceil_pos.mpr (div_pos hnum H7)
  · have Rz:=mul_le_mul TY TY H7.le (Real.exp_nonneg _)
    rw [←Real.exp_add] at Rz
    have hh:=mul_le_mul_of_nonneg_left Rz (sq_nonneg D)
    have hstrict:D^2<Real.exp (4/25*X):=by
      simp only [zero_mul,Real.exp_zero,mul_one] at KV
      have Xj:0<D^2:=sq_pos_of_pos (by linarith only [hD])
      linarith only [KV,Xj]
    have hs:=mul_lt_mul_of_pos_right hstrict (Real.exp_pos (21/50*X+21/50*X))
    rw [←Real.exp_add] at hs
    have he:4/25*X+(21/50*X+21/50*X)=X:=by ring
    rw [he] at hs
    have hsq:(D*(cE j:ℝ))^2≤D^2*Real.exp (21/50*X+21/50*X):=by
      nlinarith only [hh]
    exact (hsq.trans_lt hs).trans_le Yn
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
open Filter
lemma qo {i w:ℕ} (hi:i<w) :
    (100:ℝ)^i≤(100:ℝ)^w/100:=by
  have hh:(100:ℝ)^(i+1)≤(100:ℝ)^w:=pow_le_pow_right₀ (by norm_num) hi
  rw [pow_succ] at hh
  linarith only [hh]
lemma SH (w:ℕ):(0:ℝ)≤100^w:=by positivity
lemma jV (w:ℕ):(1:ℝ)≤100^w:=one_le_pow₀ (by norm_num)
lemma oB {a:ℝ} (ha:0≤a) (ha1:a≤1)
    (m w:ℕ) (J:ℕ → Finset ℕ)
    (hJ:∀ i<w,∀ j∈J i,(j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) :
    ∀ n∈gJ a m J w,
      (n:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)):=by
  intro n hn
  obtain ⟨i,hi,hni⟩:=M6 a m J hn
  have hh:=mul_le_mul_of_nonneg_right (qo hi) (Real.exp_nonneg (m:ℝ))
  have hi0:0≤(100:ℝ)^i*Real.exp m:=by positivity
  rcases hni with hni|hni
  · obtain ⟨j,hj,hnj⟩:=List.mem_flatMap.mp hni
    have hj':j∈J i:=(Finset.mem_sort (·≥·)).mp hj
    have hp:(2:ℝ)^j≤Real.exp (((100:ℝ)^w/50)*Real.exp m):=by
      rw [←Real.exp_log (by positivity:(0:ℝ)<2^j),Real.log_pow]
      apply Real.exp_le_exp.mpr
      nlinarith only [hJ i hi j hj',hh,hi0]
    apply Fj ha j _ n hnj
    have hc:c7*a≤1:=by
      have hg:c7≤1:=by norm_num [c7]
      exact (mul_le_mul_of_nonneg_left ha1 jg.le).trans (by simpa only [mul_one] using hg)
    exact (mul_le_of_le_one_left (by positivity:(0:ℝ)≤2^j) hc).trans hp
  · apply n8 (jM m) _ n hni
    have he:Real.exp (((100:ℝ)^i/4)*Real.exp m)≤Real.exp (((100:ℝ)^w/50)*Real.exp m):=by
      apply Real.exp_le_exp.mpr
      nlinarith only [hh,hi0]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (jM m)).trans he
lemma zP {C:ℝ} {a:ℝ} (m W:ℕ)
    (J:ℕ → Finset ℕ) (hJ:∀ w<W,((J w).card:ℝ)≤C) :
    ((gJ a m J W).length:ℝ)≤(W:ℝ)*(20*C+4*(m:ℝ)^2):=by
  induction W with
  | zero=>simp [gJ]
  | succ W ih =>
    have hi:=ih (fun w hw=>hJ w (by omega))
    rw [yQ,List.length_append,List.length_append]
    simp only [Bz,Nat.cast_add,Nat.cast_mul,e4,Nat.cast_ofNat,
      dL,List.length_ofFn,dW,Nat.cast_pow]
    have hh:=hJ W (by omega)
    have hW:(W:ℝ)+1=(W+1:ℕ):=by push_cast; rfl
    push_cast
    nlinarith only [hi,hh]
lemma qJ {a:ℝ} {m W:ℕ}
    (J:ℕ → Finset ℕ) (hm:2≤Real.exp m)
    (hJ:∀ w<W,∀ j∈J w,(j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((gJ a m J W).length:ℝ)≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2):=by
  have hb:∀ w<W,((J w).card:ℝ)≤3*(100:ℝ)^W*Real.exp m:=by
    intro w hw
    have hw1:=jV w
    have hs:2≤(100:ℝ)^w*Real.exp m:=by nlinarith only [hw1,hm]
    have hh:=q5 hs (J w) (hJ w hw)
    have hp:(100:ℝ)^w≤(100:ℝ)^W:=pow_le_pow_right₀ (by norm_num) hw.le
    have he:=mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (m:ℝ))
    nlinarith only [hh,he]
  have hh:=zP (a:=a) m W J hb
  nlinarith only [hh]
lemma BG (W:ℕ) :
    ∀ᶠ m:ℕ in atTop,
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2≤Real.exp (Real.exp m):=by
  have hp:=g9 (4*((W:ℝ)+1)) (a:=1) (by norm_num) 2
  have ht:=(i9 (a:=1) (by norm_num) (60*W*(100:ℝ)^W+3))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hp,ht] with m hm ht
  simp only [one_mul] at hm ht
  have he:1≤Real.exp (m:ℝ):=Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  nlinarith only [hm,ht,he]
noncomputable def d5 (W m:ℕ):ℕ :=
  ⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊
lemma n9 (W m:ℕ):0<d5 W m :=
  Nat.ceil_pos.mpr (Real.exp_pos _)
lemma kP (W m:ℕ) :
    Real.exp (20*(100:ℝ)^W*Real.exp m)≤(d5 W m:ℝ) ∧
    (d5 W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*Real.exp m):=by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh:=(Nat.ceil_lt_add_one (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))).le
  have he:1≤Real.exp (m:ℝ):=Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have he':3≤Real.exp (2*Real.exp (m:ℝ)):=by
    have hh:=Real.add_one_le_exp (2*Real.exp (m:ℝ))
    linarith only [hh,he]
  have hbase:1≤Real.exp (20*(100:ℝ)^W*Real.exp m):=Real.one_le_exp_iff.mpr (by positivity)
  have hmul:=mul_le_mul_of_nonneg_left he' (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hmul
  change (⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊:ℝ)+1≤_
  rw [show (20*(100:ℝ)^W+2)*Real.exp m=20*(100:ℝ)^W*Real.exp m+2*Real.exp m by ring]
  linarith only [hh,hbase,hmul]
theorem qK {D a b C:ℝ} (hD:0<D) (ha:0<a) (hab:a<b) :
    ∀ᶠ X:ℝ in atTop,∀ ns:List ℕ,∀ N:ℕ,
      1≤ns.sum+N → (ns.length+2:ℝ)≤Real.exp X →
      (∀ n∈ns,(n:ℝ)≤Real.exp (Real.exp (a*X))) →
      (N:ℝ)+1≤Real.exp (C*X) →
      Real.log 36+2*Real.log (D*(ns.sum+N))≤Real.exp (b*X):=by
  have hp:=fD
    (|Real.log 36|+2*|Real.log D|+2*|1+C|) ha 1
  have hres:=j4 hab 3
  filter_upwards [hp,hres,eventually_ge_atTop (1:ℝ)] with X hp hres hX
  intro ns N hs hl ho hN
  have hlog:=Kz ns N (Real.exp_nonneg (a*X)) ho
  have hl':Real.log ((ns.length:ℝ)+1)≤X:=by
    have hh:=Real.log_le_log (by positivity:0<(ns.length:ℝ)+1) (by linarith only [hl]:(ns.length:ℝ)+1≤Real.exp X)
    rwa [Real.log_exp] at hh
  have hN':Real.log ((N:ℝ)+1)≤C*X:=by
    have hh:=Real.log_le_log (by positivity:0<(N:ℝ)+1) hN
    rwa [Real.log_exp] at hh
  have Se:(0:ℝ)<(ns.sum+N:ℕ):=by exact_mod_cast (show 0<ns.sum+N by omega)
  have hs':Real.log ((ns.sum+N:ℕ):ℝ)≤Real.log ((ns.sum+N:ℕ)+1) :=
    Real.log_le_log Se (by push_cast; linarith)
  simp only [Nat.cast_add] at Se hs' hlog
  rw [Real.log_mul hD.ne' Se.ne']
  have hc:Real.log 36+2*Real.log D+2*(1+C)*X≤Real.exp (a*X):=by
    simp only [pow_one] at hp
    have h1:=le_abs_self (Real.log (36:ℝ))
    have h2:=le_abs_self (Real.log D)
    have h3:=le_abs_self (1+C)
    nlinarith only [hp,hX,h1,h2,h3,abs_nonneg (Real.log (36:ℝ)),abs_nonneg (Real.log D)]
  nlinarith only [hlog,hl',hN',hs',hc,hres]
noncomputable def e9 (X:ℝ):ℕ:=⌈Real.exp (X/100)⌉₊
lemma Cw (X:ℝ):0<e9 X :=
  Nat.ceil_pos.mpr (Real.exp_pos _)
lemma nY {X:ℝ} (hX:0≤X) :
    Real.exp (X/100)≤(e9 X:ℝ) ∧
    (e9 X:ℝ)≤2*Real.exp (X/100):=by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh:=(Nat.ceil_lt_add_one (Real.exp_nonneg (X/100))).le
  have he:1≤Real.exp (X/100):=Real.one_le_exp_iff.mpr (by positivity)
  change (⌈Real.exp (X/100)⌉₊:ℝ)≤2*Real.exp (X/100)
  linarith only [hh,he]
lemma xG :
    ∀ᶠ X:ℝ in atTop,∀ p:ℝ,0<p → p≤2*Real.exp (21/20*X) →
      p*Real.exp (-(e9 X:ℝ)*(1/64)^2*
        (p*Real.exp (-X/200))/(2*p))≤1/640000:=by
  have hp:=fD (8192*(21/20+Real.log (1280000:ℝ)))
    (a:=1/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X oA hX
  intro p hp0 hp
  have hlog:0≤Real.log (1280000:ℝ):=Real.log_nonneg (by norm_num)
  have pL:8192*(21/20*X+Real.log (1280000:ℝ))≤Real.exp (X/200):=by
    simp only [pow_one,show (1:ℝ)/200*X=X/200 by ring] at oA
    nlinarith only [oA,hX,hlog]
  have hn:=(nY (by linarith only [hX])).1
  have hn':=mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (-X/200))
  rw [←Real.exp_add] at hn'
  have he:X/100+-X/200=X/200:=by ring
  rw [he] at hn'
  have harg : -(e9 X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)≤
      -(21/20*X)-Real.log (1280000:ℝ):=by
    have hEq : -(e9 X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)=
        -(e9 X:ℝ)*Real.exp (-X/200)/8192:=by field_simp; ring
    rw [hEq]
    linarith only [pL,hn']
  have hh:=mul_le_mul hp (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _) (by positivity:0≤2*Real.exp (21/20*X))
  simp only [mul_assoc,←Real.exp_add] at hh
  have he':21/20*X+(-(21/20*X)-Real.log (1280000:ℝ))=-Real.log (1280000:ℝ):=by ring
  rw [he',Real.exp_neg,Real.exp_log (by norm_num:(0:ℝ)<1280000)] at hh
  norm_num at hh ⊢
  simpa only [mul_assoc] using hh
lemma tK :
    ∀ᶠ X:ℝ in atTop,∀ H b:ℝ,
      H≤Real.exp (3/50*X) → Real.exp (X/8)/(4*X)≤b →
      (e9 X:ℝ)*H/b≤1/1024:=by
  have hp:=fD (8192:ℝ) (a:=11/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X oA hX
  intro H b hH hb
  have XD:0<X:=by linarith only [hX]
  have hbp:0<b:=(div_pos (Real.exp_pos _) (by positivity)).trans_le hb
  have hn:=(nY XD.le).2
  have hmul:=(mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (e9 X))).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (3/50*X)))
  simp only [mul_assoc,←Real.exp_add] at hmul
  have hEq:X/100+3/50*X=7/100*X:=by ring
  rw [hEq] at hmul
  have hb':=(div_le_iff₀ (show 0<4*X by positivity)).mp hb
  simp only [pow_one] at oA
  have hh:=mul_le_mul_of_nonneg_right oA (Real.exp_nonneg (7/100*X))
  rw [←Real.exp_add] at hh
  have he:11/200*X+7/100*X=X/8:=by ring
  rw [he] at hh
  have Y1:(e9 X:ℝ)*H*(4096*X)≤b*(4*X):=by
    have hh':=mul_le_mul_of_nonneg_right hmul (show 0≤4096*X by positivity)
    nlinarith only [hh',hh,hb']
  apply (div_le_iff₀ hbp).mpr
  nlinarith only [Y1,XD]
lemma rO {c:ℝ} (hc:0<c) :
    ∀ᶠ X:ℝ in atTop,∀ n H T:ℝ,
      0≤n → n≤Real.exp (7/10*X) → H≤Real.exp (13/50*X) → Real.exp X≤T →
      2*n*H≤c*T/5000:=by
  have hh:=j4 (a:=24/25) (b:=1) (by norm_num) (10000/c)
  filter_upwards [hh] with X hX
  intro n H T hn0 hn hH hT
  have hmul:=(mul_le_mul_of_nonneg_left hH hn0).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (13/50*X)))
  rw [←Real.exp_add] at hmul
  have he:7/10*X+13/50*X=24/25*X:=by ring
  rw [he] at hmul
  simp only [one_mul] at hX
  have hh':=mul_le_mul_of_nonneg_left (hX.trans hT) hc.le
  rw [←mul_assoc,mul_div_cancel₀ _ hc.ne'] at hh'
  nlinarith only [hmul,hh']
theorem wJ (s:aE) (D X:ℝ) (N:ℕ)
    (mid bot:List ℕ) (b q:ℕ) (e:ℝ)
    (hm:fq s D mid 0 b e) (hb:fq s D bot N q e)
    (jE:0< s.aP) (hN:1≤bot.sum+N)
    (hX:100≤X)
    (hp:∀ i,Real.exp X≤(s.bD i:ℝ) ∧
      (s.bD i:ℝ)≤2*Real.exp (21/20*X))
    (hbase:e*s.aP≤Real.exp (-100)/(512*640000))
    (hmid:e*s.aP≤1/1024)
    (jz:(e9 X:ℝ)*(Real.log 36+2*Real.log (D*(bot.sum+N)))/b≤1/1024)
    (O1:∀ i,(s.bD i:ℝ)*Real.exp
      (-(e9 X:ℝ)*(1/64)^2*
        ((s.bD i:ℝ)*Real.exp (-X/200))/(2*(s.bD i:ℝ)))≤1/640000) :
    gG s D N (mid++bot) (1/4)
      (fun i=>(s.bD i:ℝ)*Real.exp (-X/200)) (1/100):=by
  exact Ly s D N mid bot b q (e9 X) e e _ hm hb
    (hm.size_pos jE) (hm.M5 jE) (hb.size_pos jE) (hb.M5 jE)
    hN (Cw X)
    (fun i=>(Real.exp_le_exp.mpr hX).trans (hp i).1)
    (fun i=>mul_pos ((Real.exp_pos X).trans_le (hp i).1) (Real.exp_pos _)) hbase
    (by linarith only [hmid,jz]) O1
lemma Ie {t Y:ℝ} (ht:0≤t) (hY:1≤Y)
    (htY:t≤Real.exp (-Y)) :
    Real.binEntropy t≤(Y+1)*Real.exp (-Y):=by
  have heY:2≤Real.exp Y:=by linarith only [Real.add_one_le_exp Y,hY]
  have hu:Real.exp (-Y)≤(1/2:ℝ):=by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using heY)
  have hm:=Real.binEntropy_strictMonoOn.monotoneOn
    (show t∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨ht,htY.trans hu⟩)
    (show Real.exp (-Y)∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨(Real.exp_pos _).le,hu⟩) htY
  have hn:=Real.negMulLog_le_one_sub_self (show 0≤1-Real.exp (-Y) by linarith only [hu])
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog,Real.log_exp] at hm ⊢
  have hh : -(1-Real.exp (-Y))*Real.log (1-Real.exp (-Y))≤Real.exp (-Y):=by
    simpa only [Real.negMulLog,sub_sub_cancel] using hn
  nlinarith only [hm,hh]
lemma Od {a N X A:ℝ} (ha:a≤Real.exp (A*X))
    (hN:Real.exp (10*A*X)≤N) :
    a/(N+1)≤Real.exp (-9*A*X):=by
  have hNp:0<N+1:=by linarith only [hN,Real.exp_pos (10*A*X)]
  apply (div_le_iff₀ hNp).mpr
  have hh:=mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-9*A*X))
  rw [←Real.exp_add] at hh
  rw [show -9*A*X+10*A*X=A*X by ring] at hh
  nlinarith only [ha,hh,Real.exp_nonneg (-9*A*X)]
theorem xO {A H:ℝ} (hA:1≤A) :
    ∀ᶠ X:ℝ in atTop,∀ a L E N:ℝ,
      0≤a → a≤Real.exp (A*X) → 0≤L → L≤Real.exp (A*X) →
      E≤Real.exp (A*X) → Real.exp (10*A*X)≤N →
      2*Real.binEntropy (a/(N+1))+(a/(N+1))*(L*H+2*E)≤Real.exp (-X):=by
  have oA:=fD (4*(9*A+1))
    (a:=9*A-1) (by linarith only [hA]) 1
  have jz:=fD (2*(max H 0+2))
    (a:=8*A-1) (by linarith only [hA]) 0
  filter_upwards [oA,jz,eventually_ge_atTop (1:ℝ)] with X oA jz hX
  intro a L E N ha0 ha hL0 hL hE hN
  have Sh:0<N+1:=by linarith only [hN,Real.exp_pos (10*A*X)]
  have ht0:0≤a/(N+1):=div_nonneg ha0 Sh.le
  have ht:=Od ha hN
  have Y3:1≤A*X:=by nlinarith only [hA,hX]
  have RP:=Ie ht0 (by nlinarith only [Y3]:1≤9*A*X)
    (by simpa only [neg_mul] using ht)
  have Xk:2*Real.binEntropy (a/(N+1))≤Real.exp (-X)/2:=by
    simp only [pow_one] at oA
    have hc:4*(9*A*X+1)≤Real.exp ((9*A-1)*X):=by nlinarith only [oA,hX]
    have hh:=mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-(9*A*X)))
    rw [←Real.exp_add,show (9*A-1)*X+-(9*A*X)= -X by ring] at hh
    linarith only [hh,RP]
  have hK:L*H+2*E≤(max H 0+2)*Real.exp (A*X):=by
    have hh:=mul_le_mul_of_nonneg_left (le_max_left H 0) hL0
    have hh':=mul_le_mul_of_nonneg_right hL (le_max_right H 0)
    nlinarith only [hh,hh',hE]
  have hKt:=(mul_le_mul_of_nonneg_left hK ht0).trans
    (mul_le_mul_of_nonneg_right ht (show 0≤(max H 0+2)*Real.exp (A*X) by positivity))
  have hprod:Real.exp (-9*A*X)*((max H 0+2)*Real.exp (A*X))=
      (max H 0+2)*Real.exp (-8*A*X):=by
    rw [mul_left_comm,←Real.exp_add]
    congr 1
    ring_nf
  rw [hprod] at hKt
  have hlast:(max H 0+2)*Real.exp (-8*A*X)≤Real.exp (-X)/2:=by
    simp only [pow_zero,mul_one] at jz
    have hh:=mul_le_mul_of_nonneg_right jz (Real.exp_nonneg (-8*A*X))
    rw [←Real.exp_add,show (8*A-1)*X+-8*A*X= -X by ring] at hh
    linarith only [hh]
  linarith only [Xk,hKt,hlast]
lemma xP (C:ℝ) :
    ∀ᶠ X:ℝ in atTop,C*X*Real.exp (-X)≤1:=by
  have hh:=g9 C (a:=1) (by norm_num) 1
  filter_upwards [hh] with X hX
  simp only [pow_one,one_mul] at hX
  have hm:=mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (-X))
  simpa only [←Real.exp_add,add_neg_cancel,Real.exp_zero] using hm
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
open Filter
noncomputable def g6 (a:ℝ) (m W:ℕ) (J:ℕ → Finset ℕ):List ℕ :=
  gJ a m J W++dL m (1/20)
noncomputable def jt (a:ℝ) (m w:ℕ) (J:ℕ → Finset ℕ):List ℕ :=
  dL m ((100:ℝ)^w/4)++gJ a m J w
lemma lQ (w:ℕ) :
    Tendsto (fun m:ℕ=>(100:ℝ)^w*Real.exp m) atTop atTop :=
  (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
lemma oc (j:ℕ) :
    ∀ p∈(cP j).primes,(2:ℝ)^j≤(p:ℝ) ∧ (p:ℝ)≤2*(2:ℝ)^j:=by
  intro p hp
  have hh:=(dS.iw j p).mp hp
  constructor
  · exact_mod_cast hh.1
  · have hh':p≤2^(j+1):=hh.2.1.le
    rw [pow_succ] at hh'
    exact_mod_cast (by simpa only [mul_comm] using hh':p≤2*2^j)
lemma rE {δ:ℝ} (hδ:0<δ) {j:ℕ}
    (hd:δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card) :
    (cP j).primes.Nonempty:=by
  apply Finset.card_pos.mp
  have hp:0<δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)):=by rw [Real.log_pow]; positivity
  exact_mod_cast hp.trans_le hd
lemma wL {X:ℝ} (hX:2≤X) {j:ℕ}
    (hne:(cP j).primes.Nonempty)
    (hlo:X≤j*Real.log 2) (hhi:j*Real.log 2≤21/20*X) :
    1≤(cP j).aP ∧ (cP j).aP≤2*X:=by
  have hh:=(cP j).m5 hne (by positivity) (oc j)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
  have hl2:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  constructor <;> linarith only [hh.1,hh.2,hlo,hhi,hX,hl2]
lemma JE {a:ℝ} {m W:ℕ} (J:ℕ → Finset ℕ) (hm:2≤Real.exp m)
    (hJ:∀ w<W,∀ j∈J w,(j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((g6 a m W J).length:ℝ)+2≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2:=by
  have hh:=qJ (a:=a) J hm hJ
  simp only [g6,List.length_append,dL,List.length_ofFn,
    dW,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linarith only [hh]
lemma D9 {a:ℝ} {m W w:ℕ} (J:ℕ → Finset ℕ) (hw:w<W) :
    (jt a m w J).length≤(gJ a m J W).length:=by
  obtain ⟨pre,he⟩:=oY a m J hw
  simp only [jt,he,List.length_append]
  omega
theorem mJ {D a:ℝ} (hD:1≤D) (ha:0≤a) (ha1:a≤1)
    (W w:ℕ) (hw:w<W) :
    ∀ᶠ m:ℕ in atTop,∀ J:ℕ → Finset ℕ,
      (∀ i<W,∀ j∈J i,(j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) →
      ((g6 a m W J).length:ℝ)+2≤Real.exp (Real.exp m) ∧
      (d5 W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) ∧
      ((gJ a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) ∧
      Real.log 36+2*Real.log (D*((dL m (1/20)).sum+d5 W m))≤
        Real.exp (3/50*((100:ℝ)^w*Real.exp m)) ∧
      Real.log 36+2*Real.log (D*((jt a m w J++dL m (1/20)).sum+d5 W m))≤
        Real.exp (13/50*((100:ℝ)^w*Real.exp m)):=by
  have hN:=i9 (a:=1/100) (by norm_num) (20*(100:ℝ)^W+2)
  have hlen:=i9 (a:=1/100) (by norm_num) 1
  have ht:=lQ w
  have hbot:=ht.eventually (qK (D:=D) (a:=1/20) (b:=3/50)
    (C:=20*(100:ℝ)^W+2) (by linarith only [hD]) (by norm_num) (by norm_num))
  have hrest:=ht.eventually (qK (D:=D) (a:=1/4) (b:=13/50)
    (C:=20*(100:ℝ)^W+2) (by linarith only [hD]) (by norm_num) (by norm_num))
  have hm2:=(lQ 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [BG W,hN,hlen,hbot,hrest,hm2] with m hm hN hlen hbot hrest hm2
  intro J hJ
  simp only [one_mul] at hlen
  simp only [pow_zero,one_mul] at hm2
  have hl:=(JE (a:=a) J hm2 hJ).trans hm
  have hpow:=jV w
  have hX:Real.exp (m:ℝ)≤(100:ℝ)^w*Real.exp m:=by nlinarith only [hpow,Real.exp_pos (m:ℝ)]
  have Vg:(d5 W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)):=by
    have hN':=(kP W m).2.trans (Real.exp_le_exp.mpr hN)
    linarith only [hN']
  have Y4:((gJ a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)):=by
    have hh:(gJ a m J w).length≤(g6 a m W J).length:=by
      obtain ⟨pre,he⟩:=oY a m J hw
      simp only [g6,he,List.length_append]; omega
    have harg:Real.exp (m:ℝ)≤Real.exp (((100:ℝ)^w/50)*Real.exp m):=by
      apply hlen.trans (Real.exp_le_exp.mpr _)
      nlinarith only [hpow,Real.exp_pos (m:ℝ)]
    exact (add_le_add (by exact_mod_cast hh:((gJ a m J w).length:ℝ)≤(g6 a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr harg))
  have hNs:(d5 W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*((100:ℝ)^w*Real.exp m)) :=
    (kP W m).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX (by positivity)))
  have Xl:((dL m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m):=by
    have hh:(dL m (1/20)).length≤(g6 a m W J).length:=by simp [g6]
    exact (add_le_add (by exact_mod_cast hh:((dL m (1/20)).length:ℝ)≤(g6 a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have Xm:((jt a m w J++dL m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m):=by
    have hh:=D9 (a:=a) (m:=m) J hw
    have hh':(jt a m w J++dL m (1/20)).length≤(g6 a m W J).length:=by
      simp only [g6,List.length_append]; omega
    exact (add_le_add (by exact_mod_cast hh':((jt a m w J++dL m (1/20)).length:ℝ)≤(g6 a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have UZ:∀ n∈dL m (1/20),(n:ℝ)≤Real.exp (Real.exp ((1/20)*((100:ℝ)^w*Real.exp m))):=by
    apply n8 (jM m)
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (jM m)).trans
      (Real.exp_le_exp.mpr (by linarith only [hX]))
  have Xn:∀ n∈jt a m w J++dL m (1/20),(n:ℝ)≤Real.exp (Real.exp ((1/4)*((100:ℝ)^w*Real.exp m))):=by
    intro n hn
    rcases List.mem_append.mp hn with hn|hn
    · rcases List.mem_append.mp hn with hn|hn
      · apply n8 (jM m) _ n hn
        simpa only [div_mul_eq_mul_div,mul_assoc,one_mul] using
          (mul_le_of_le_one_left (Real.exp_nonneg (((100:ℝ)^w/4)*Real.exp m)) (jM m))
      · exact (oB ha ha1 m w J (fun i hi=>hJ i (hi.trans hw)) n hn).trans
          (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity]:((100:ℝ)^w/50)*Real.exp m≤(1/4)*((100:ℝ)^w*Real.exp m))))
    · exact (UZ n hn).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity]:(1/20)*((100:ℝ)^w*Real.exp m)≤(1/4)*((100:ℝ)^w*Real.exp m))))
  exact ⟨hl,Vg,Y4,
    hbot _ _ (by have:=n9 W m; omega) Xl UZ hNs,
    hrest _ _ (by have:=n9 W m; omega) Xm Xn hNs⟩
lemma M7 {s:aE} {g U X:ℝ} {l:ℕ}
    (hX:0<X) (hm:0<s.aP) (hm':s.aP≤2*X)
    (jR:Real.exp (X/8)≤aW g U l) (cQ:4*X≤Real.exp (X/8)) :
    Real.exp (X/8)/(4*X)≤(eD s g U l:ℝ):=by
  have hf:=Nat.lt_floor_add_one (aW g U l/s.aP)
  have hh:=mul_lt_mul_of_pos_right hf hm
  rw [div_mul_cancel₀ _ hm.ne',add_mul,one_mul] at hh
  have hb:=mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (eD s g U l))
  change (aW g U l)<((eD s g U l:ℝ)*s.aP)+s.aP at hh
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hf,hh,hb,jR,cQ,hm']
theorem Cz {D a δ:ℝ} (hD:1≤D) (ha:0≤a) (ha1:a≤1)
    (hδ:0<δ) (W w:ℕ) (hw:w<W) :
    ∀ᶠ m:ℕ in atTop,∀ J:ℕ → Finset ℕ,
      (∀ i<W,∀ j∈J i,((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card) →
      ∀ j∈J w,
        Nonempty (fq (cP j) D (jt a m w J) 0
          (eD (cP j) (dH m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (dW m))
          (91*dH m)) ∧
        Nonempty (fq (cP j) D (dL m (1/20)) (d5 W m)
          (eD (cP j) (dH m) (Real.exp ((1/20)*Real.exp m)) (dW m))
          (91*dH m)) ∧
        Real.exp (((100:ℝ)^w*Real.exp m)/8)/(4*((100:ℝ)^w*Real.exp m))≤
          (eD (cP j) (dH m) (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (dW m):ℝ):=by
  have hwp:=jV w
  have hp:(0:ℝ)<100^w:=by positivity
  have hmid:=oX (D:=D) (A:=(100:ℝ)^w) (B:=2*(100:ℝ)^w)
    (a:=(100:ℝ)^w/4) (b:=(100:ℝ)^w/50) hD hp (by positivity) (by linarith only [hp])
    (by linarith only [hp]) hδ
  have hbot:=oX (D:=D) (A:=1) (B:=2*(100:ℝ)^w)
    (a:=1/20) (b:=1/100) hD (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ
  have jR:=k5 (a:=(100:ℝ)^w/4) (by positivity) 0
  have cQ:=i9 (a:=(100:ℝ)^w/8) (by positivity) (4*(100:ℝ)^w)
  have hm2:=(lQ 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [hmid,hbot,jR,cQ,mJ hD ha ha1 W w hw,hm2]
    with m hmid hbot jR cQ htail hm2
  intro J hJ j hj
  simp only [pow_zero,one_mul] at hm2
  have kC:=hJ w hw j hj
  have hne:=rE hδ kC.2.2
  have hX2:2≤(100:ℝ)^w*Real.exp m:=by nlinarith only [hm2,hwp]
  have hm:=wL hX2 hne kC.1 kC.2.1
  have hpj:=oc j
  have hdense:δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(cP j).primes.card:=by
    change δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤(dS.d6 j).card
    simpa only [pow_succ,mul_comm] using kC.2.2
  have hT:Real.exp ((100:ℝ)^w*Real.exp m)≤(2:ℝ)^j:=by
    rw [←Real.exp_log (by positivity:(0:ℝ)<2^j),Real.log_pow]
    exact Real.exp_le_exp.mpr kC.1
  have R9:Real.log ((2:ℝ)^j)≤(2*(100:ℝ)^w)*Real.exp m:=by
    rw [Real.log_pow]
    nlinarith only [kC.2.1,hX2]
  obtain ⟨_,hN,hlen,_,_⟩:=htail J (fun i hi k hk=>(hJ i hi k hk).2.1)
  have Xo:=hmid (cP j) ((2:ℝ)^j) [] (gJ a m J w) 0
    hne hpj hdense hT R9
    (oB ha ha1 m w J (fun i hi k hk=>(hJ i (hi.trans hw) k hk).2.1))
    (by simp only [Nat.cast_zero]; positivity) hlen
  have Yo:(2:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)):=by
    have he:1≤Real.exp ((1/100)*Real.exp (m:ℝ)):=Real.one_le_exp_iff.mpr (by positivity)
    linarith only [Real.add_one_le_exp (Real.exp ((1/100)*Real.exp (m:ℝ))),he]
  have Xp:=hbot (cP j) ((2:ℝ)^j) [] [] (d5 W m)
    hne hpj hdense
    ((Real.exp_le_exp.mpr (by nlinarith only [hwp,Real.exp_pos (m:ℝ)]:1*Real.exp m≤(100:ℝ)^w*Real.exp m)).trans hT)
    R9 (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]) hN
    (by simpa only [List.length_nil,Nat.cast_zero,zero_add] using Yo)
  refine ⟨?_,?_,?_⟩
  · simpa only [List.nil_append,dL,jt] using Xo
  · simpa only [List.nil_append,List.append_nil,dL] using Xp
  · apply M7 (by linarith only [hX2]) (by linarith only [hm.1]) hm.2
    · simpa only [pow_zero,one_mul,div_div,show (4:ℝ)*2=8 by norm_num,div_mul_eq_mul_div] using jR
    · simpa only [mul_assoc,div_mul_eq_mul_div] using cQ
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
open Filter
lemma wM :
    ∀ᶠ X:ℝ in atTop,∀ p L N:ℝ,
      0<p → p≤2*Real.exp (21/20*X) → 0≤L → L≤Real.exp (21/50*X) →
      Real.exp (20*X)≤N → L≤N ∧ L/(N+1)≤((1/4)/p)/2:=by
  have hh:=j4 (a:=147/100) (b:=20) (by norm_num) 16
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with X hh hX
  intro p L N hp hp' hL hL' hN
  have Sh:0<N+1:=by linarith only [hN,Real.exp_pos (20*X)]
  have hm:=mul_le_mul hp' hL' hL (by positivity:0≤2*Real.exp (21/20*X))
  rw [mul_assoc,←Real.exp_add,show 21/20*X+21/50*X=147/100*X by ring] at hm
  refine ⟨hL'.trans ((Real.exp_le_exp.mpr (by linarith only [hX])).trans hN),?_⟩
  apply (div_le_iff₀ Sh).mpr
  have he:((1/4:ℝ)/p)/2=(1/8)/p:=by ring
  rw [he]
  apply (mul_le_mul_iff_left₀ hp).mp
  have heq:(1/8/p)*(N+1)*p=(N+1)/8:=by field_simp
  rw [heq]
  nlinarith only [hm,hh,hN]
theorem CH {D a δ:ℝ} {K:ℕ}
    (hD:1≤D) (ha:0<a) (ha1:a≤1) (KI:2*a≤δ)
    (jI:a≤(2:ℝ)^K*cZ a) (W w:ℕ) (hw:w<W) :
    ∀ᶠ m:ℕ in atTop,∀ J:ℕ → Finset ℕ,
      (∀ i<W,∀ j∈J i,((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card) →
      (∀ i∈J w,∀ j∈J w,i<j → i+K≤j) →
      ∀ j∈J w,∀ E:ℝ,E≤(cZ a/4)*(2:ℝ)^j/10000 →
        Nonempty (kL D (g6 a m W J) (d5 W m)
          (cP j) (cE j) E
          ((cZ a/4)/(10000000*Real.log ((2:ℝ)^j)))):=by
  have hδ:0<δ:=by linarith only [ha,KI]
  have hc:0<cZ a/4:=by exact div_pos (jZ ha) (by norm_num)
  have ht:=lQ w
  have hε:0 < min (1/1024:ℝ) (Real.exp (-100)/(512*640000)):=by positivity
  have iJ:=zL (2*(100:ℝ)^w) hε
  filter_upwards [Cz hD ha.le ha1 hδ W w hw,
    mJ hD ha.le ha1 W w hw,
    ht.eventually (Fo hD ha KI jI),
    ht.eventually (rJ hD),
    ht.eventually xG,ht.eventually tK,
    ht.eventually (rO hc),
    ht.eventually wM,iJ,ht.eventually (eventually_ge_atTop (1600:ℝ))]
    with m Wk htail htop hint O1 Wm Wn hsmooth iJ hX
  intro J hJ hsep j hj E hE
  let X:ℝ:=(100:ℝ)^w*Real.exp m
  let s:=cP j
  have kC:=hJ w hw j hj
  have hne:s.primes.Nonempty:=rE hδ kC.2.2
  have hpj:=oc j
  have hm:=wL (by linarith only [hX]) hne kC.1 kC.2.1
  have o9:(0:ℝ)<2^j:=by positivity
  have hT:Real.exp X≤(2:ℝ)^j:=by
    rw [←Real.exp_log o9,Real.log_pow]
    exact Real.exp_le_exp.mpr kC.1
  have hprime:∀ i:s.bZ,Real.exp X≤(s.bD i:ℝ) ∧
      (s.bD i:ℝ)≤2*Real.exp (21/20*X):=by
    intro i
    have hp:=hpj _ (s.enumeration i.2).property
    refine ⟨hT.trans hp.1,hp.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [←Real.exp_log o9,Real.log_pow]
    exact Real.exp_le_exp.mpr kC.2.1
  obtain ⟨pre,hpre⟩:=oY a m J hw
  obtain ⟨Ob,QN⟩:=htop (J w) pre hsep (hJ w hw) j hj
  obtain ⟨Wq⟩:=Ob
  obtain ⟨hmid,hbot,Xq⟩:=Wk J hJ j hj
  obtain ⟨Yp⟩:=hmid
  obtain ⟨Yq⟩:=hbot
  obtain ⟨_,_,_,T8,S9⟩:=htail J (fun i hi k hk=>(hJ i hi k hk).2.1)
  have RA:(91*dH m)*s.aP≤ min (1/1024:ℝ) (Real.exp (-100)/(512*640000)):=by
    have hh:=mul_le_mul_of_nonneg_left hm.2 (by have:=nT m; positivity:0≤91*dH m)
    exact hh.trans (by simpa only [mul_assoc] using iJ)
  have Tf:=wJ s D X (d5 W m)
    (jt a m w J) (dL m (1/20)) _ _ _ Yp Yq
    (by linarith only [hm.1]) (by have:=n9 W m; omega)
    (by linarith only [hX]) hprime
    (RA.trans (min_le_right _ _)) (RA.trans (min_le_left _ _))
    (Wm _ _ T8 Xq) (fun i=>O1 _ ((Real.exp_pos X).trans_le (hprime i).1) (hprime i).2)
  obtain ⟨hn,j6,Y5,Yr,Xr,U3⟩:=hint j kC.1 kC.2.1
  have hN:Real.exp (20*X)≤(d5 W m:ℝ):=by
    apply le_trans _ (kP W m).1
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤100) hw.le) (Real.exp_nonneg (m:ℝ))
    dsimp only [X]
    nlinarith only [hh]
  have T9:cE j≤d5 W m:=by
    have h:=hsmooth ((2:ℝ)^j) (cE j) (d5 W m) o9
      (by
        have hh:(2:ℝ)^j≤Real.exp (21/20*X):=by
          rw [←Real.exp_log o9,Real.log_pow]
          exact Real.exp_le_exp.mpr kC.2.1
        linarith only [hh,Real.exp_nonneg (21/20*X)])
      (Nat.cast_nonneg _) U3 hN
    exact_mod_cast h.1
  refine ⟨{
    pre:=pre++j3 a (J w)
    rest:=jt a m w J++dL m (1/20)
    schedule:=by simp only [g6,jt,hpre,List.append_assoc]
    T:=(2:ℝ)^j
    nonempty:=hne
    LJ:=hpj
    large:=by linarith only [hT,Real.add_one_le_exp X,hX]
    mean:=hm.1
    b:=eD s c7 (a*(2:ℝ)^j) e4
    n:=gI j
    τ:=1/4
    A:=X/400
    η:=1/100
    δ:=1/10000
    u:=fun i=>(s.bD i:ℝ)*Real.exp (-X/200)
    DZ:=Wq
    coverage:=Tf
    cap:=Wq.M5 (by linarith only [hm.1])
    repetitions:=hn
    length:=uj j
    floor:=by norm_num
    gain:=by linarith only [hX]
    exceptions:=fun i=>by positivity
    short:=fun i=>j6.trans_le (hpj _ (s.enumeration i.2).property).1
    xB:=T9
    Ky:=fun i=>(hsmooth _ _ _ ((Real.exp_pos X).trans_le (hprime i).1)
      (hprime i).2 (Nat.cast_nonneg _) U3 hN).2
    list:=?_
    rate:=?_
  }⟩
  · intro i
    have hh:=Cu hX hT ((Real.exp_pos X).trans_le (hprime i).1)
      (hpj _ (s.enumeration i.2).property).2 Y5
    dsimp only [s] at hh
    convert hh using 1; congr 2; ring_nf
  · apply Cv (by linarith only [hX]) o9 hc
      (by simpa only [Real.log_pow] using kC.1)
      (by simpa only [Real.log_pow] using kC.2.1) hm.2
      (by convert QN using 1; ring) Yr
      (Wn _ _ _ (Nat.cast_nonneg _) Xr S9 hT) hE
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
section
open scoped BigOperators Classical
noncomputable def jw (J:Finset ℕ) (n:ℕ):ℕ :=
  if h:n<J.card then J.orderEmbOfFin rfl ⟨n,h⟩ else 0
lemma zQ (J:Finset ℕ) {n:ℕ} (hn:n<J.card) :
    jw J n=J.orderEmbOfFin rfl ⟨n,hn⟩:=by simp only [jw,JG hn]
lemma mC (J:Finset ℕ) {n:ℕ} (hn:n<J.card):jw J n∈J:=by
  rw [zQ J hn]
  exact J.orderEmbOfFin_mem rfl _
lemma l9 (J:Finset ℕ) {n k:ℕ} (hnk:n<k) (hk:k<J.card) :
    jw J n<jw J k:=by
  rw [zQ J (hnk.trans hk),zQ J hk]
  exact (J.orderEmbOfFin rfl).strictMono hnk
lemma KQ (J:Finset ℕ) {j:ℕ} (hj:j∈J) :
    ∃ n<J.card,jw J n=j:=by
  have hh:j∈Set.range (J.orderEmbOfFin rfl):=by rw [J.range_orderEmbOfFin rfl]; exact hj
  obtain ⟨i,hi⟩:=hh
  exact ⟨i.val,i.isLt,(zQ J i.isLt).trans hi⟩
lemma Rq (J:Finset ℕ) (f:ℕ → ℝ) :
    (∑ n∈Finset.range J.card,f (jw J n))=∑ j∈J,f j:=by
  apply Finset.sum_bij (fun n _=>jw J n)
  · intro n hn; exact mC J (Finset.mem_range.mp hn)
  · intro n hn k hk he
    have hn':=Finset.mem_range.mp hn
    have hk':=Finset.mem_range.mp hk
    rcases lt_trichotomy n k with h|h|h
    · exact (ne_of_lt (l9 J h hk') he).elim
    · exact h
    · exact (ne_of_lt (l9 J h hn') he.symm).elim
  · intro j hj
    obtain ⟨n,hn,he⟩:=KQ J hj
    exact ⟨n,Finset.mem_range.mpr hn,he⟩
  · intro n hn; rfl
lemma vE (J:Finset ℕ) {n:ℕ} (hn:n<J.card) :
    gd (fun k=>cP (jw J k)) n⊆
      (J.filter (·<jw J n)).biUnion (fun j=>(cP j).e6):=by
  intro f hf
  obtain ⟨k,hk,hf⟩:=Finset.mem_biUnion.mp hf
  have hk':=Finset.mem_range.mp hk
  apply Finset.mem_biUnion.mpr
  exact ⟨jw J k,Finset.mem_filter.mpr ⟨mC J (hk'.trans hn),l9 J hk' hn⟩,hf⟩
lemma xQ (J:Finset ℕ) {K n:ℕ} (hK:0<K) (hn:n<J.card)
    (hsep:∀ a∈J,∀ b∈J,a<b → a+K≤b) :
    c8 (gd (fun k=>cP (jw J k)) n)≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^(jw J n):=by
  apply (oT (vE J hn)).trans
  apply Fk _ hK
  · intro a ha b hb hab
    exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  · intro a ha
    exact hsep a (Finset.mem_filter.mp ha).1 (jw J n) (mC J hn) (Finset.mem_filter.mp ha).2
lemma zR (J:Finset ℕ) :
    gd (fun k=>cP (jw J k)) J.card=
      J.biUnion (fun j=>(cP j).e6):=by
  ext f
  constructor
  · intro hf
    obtain ⟨k,hk,hf⟩:=Finset.mem_biUnion.mp hf
    exact Finset.mem_biUnion.mpr ⟨jw J k,mC J (Finset.mem_range.mp hk),hf⟩
  · intro hf
    obtain ⟨j,hj,hf⟩:=Finset.mem_biUnion.mp hf
    obtain ⟨n,hn,he⟩:=KQ J hj
    exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr hn,by simpa only [he] using hf⟩
open scoped BigOperators Classical
open Filter
noncomputable def jN (W:ℕ) (J:ℕ → Finset ℕ):Finset ℕ :=
  (Finset.range W).biUnion J
lemma Fp {X:ℝ} {K u v i j:ℕ} (hX:0<X)
    (hK:K*Real.log 2≤X) (huv:u<v)
    (hi:i*Real.log 2≤21/20*((100:ℝ)^u*X))
    (hj:(100:ℝ)^v*X≤j*Real.log 2):i+K≤j:=by
  have hp:=mul_le_mul_of_nonneg_right (qo huv) hX.le
  have ho:=jV u
  have hu:X≤(100:ℝ)^u*X:=by nlinarith only [ho,hX]
  have hh:((i+K:ℕ):ℝ)*Real.log 2≤(j:ℝ)*Real.log 2:=by
    push_cast
    nlinarith only [hp,hu,hK,hi,hj,hX]
  have hl:0<Real.log 2:=Real.log_pos (by norm_num)
  have hn:(i+K:ℕ)≤(j:ℝ):=(mul_le_mul_iff_left₀ hl).mp hh
  exact_mod_cast hn
lemma Lz {X:ℝ} {K W:ℕ} (J:ℕ → Finset ℕ) (hX:0<X)
    (hK:K*Real.log 2≤X)
    (hb:∀ w<W,∀ j∈J w,(100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hsep:∀ w<W,∀ i∈J w,∀ j∈J w,i<j → i+K≤j) :
    ∀ i∈jN W J,∀ j∈jN W J,i<j → i+K≤j:=by
  intro i hi j hj hij
  obtain ⟨u,hu,hi⟩:=Finset.mem_biUnion.mp hi
  obtain ⟨v,hv,hj⟩:=Finset.mem_biUnion.mp hj
  have hu':=Finset.mem_range.mp hu
  have hv':=Finset.mem_range.mp hv
  rcases lt_trichotomy u v with huv|rfl|hvu
  · exact Fp hX hK huv (hb u hu' i hi).2 (hb v hv' j hj).1
  · exact hsep u hu' i hi j hj hij
  · have hh:=Fp hX hK hvu (hb v hv' j hj).2 (hb u hu' i hi).1
    omega
lemma Qb {X:ℝ} {W:ℕ} (J:ℕ → Finset ℕ) (hX:0<X)
    (hb:∀ w<W,∀ j∈J w,(100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X)) :
    (↑(Finset.range W):Set ℕ).PairwiseDisjoint J:=by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro j hju XE
  have hp (i k:ℕ) (hik:i<k) (hji:j∈J i) (hjk:j∈J k) (hi:i<W) (hk:k<W):False:=by
    have hh:=mul_le_mul_of_nonneg_right (qo hik) hX.le
    have hlo:=(hb k hk j hjk).1
    have hhi:=(hb i hi j hji).2
    have hz:0<(100:ℝ)^k*X:=by positivity
    nlinarith only [hh,hlo,hhi,hz]
  rcases lt_or_gt_of_ne hne with h|h
  · exact hp u v h hju XE (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  · exact hp v u h XE hju (Finset.mem_range.mp hv) (Finset.mem_range.mp hu)
lemma wN {m W:ℕ} (J:ℕ → Finset ℕ) (hm:2≤Real.exp m)
    (hb:∀ w<W,∀ j∈J w,j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((jN W J).card:ℝ)≤3*(W:ℝ)*(100:ℝ)^W*Real.exp m:=by
  have hh:=Finset.card_biUnion_le (s:=Finset.range W) (t:=J)
  have hs:(∑ w∈Finset.range W,((J w).card:ℝ))≤(W:ℝ)*(3*(100:ℝ)^W*Real.exp m):=by
    calc
      _ ≤ ∑ w∈Finset.range W,3*(100:ℝ)^W*Real.exp m:=by
        apply Finset.sum_le_sum
        intro w hw
        have hw':=Finset.mem_range.mp hw
        have hp:=jV w
        have he:2≤(100:ℝ)^w*Real.exp m:=by nlinarith only [hp,hm]
        have hc:=q5 he (J w) (hb w hw')
        have hp':=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
        nlinarith only [hc,hp']
      _ = _:=by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hh':((jN W J).card:ℝ)≤∑ w∈Finset.range W,((J w).card:ℝ):=by exact_mod_cast hh
  nlinarith only [hh',hs]
lemma QO {X c t:ℝ} {W:ℕ} (J:ℕ → Finset ℕ) (hX:0<X) (hc:0<c)
    (hb:∀ w<W,∀ j∈J w,(100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hdense:∀ w<W,t*((100:ℝ)^w*X)≤(J w).card) :
    (W:ℝ)*(c*t/10500000)≤∑ j∈jN W J,c/(10000000*Real.log ((2:ℝ)^j)):=by
  rw [jN,Finset.sum_biUnion (Qb J hX hb)]
  have hs:∀ w<W,c*t/10500000≤∑ j∈J w,c/(10000000*Real.log ((2:ℝ)^j)):=by
    intro w hw
    have Y6:0<(100:ℝ)^w*X:=by positivity
    have hl:∀ j∈J w,0<Real.log ((2:ℝ)^j):=by
      intro j hj; rw [Real.log_pow]; exact Y6.trans_le (hb w hw j hj).1
    have ht':=hdense w hw
    have hh:(J w).card*(c/(10500000*((100:ℝ)^w*X)))≤∑ j∈J w,c/(10000000*Real.log ((2:ℝ)^j)):=by
      calc
        _ = ∑ _j∈J w,c/(10500000*((100:ℝ)^w*X)):=by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _:=by
          apply Finset.sum_le_sum
          intro j hj
          apply div_le_div_of_nonneg_left hc.le (by have:=hl j hj; positivity:0<10000000*Real.log ((2:ℝ)^j))
          rw [Real.log_pow]
          nlinarith only [(hb w hw j hj).2]
    have hm:=mul_le_mul_of_nonneg_right ht' (show 0≤c/(10500000*((100:ℝ)^w*X)) by positivity)
    have he:t*((100:ℝ)^w*X)*(c/(10500000*((100:ℝ)^w*X)))=c*t/10500000:=by field_simp
    rw [he] at hm
    exact hm.trans hh
  have hh:=Finset.sum_le_sum (s:=Finset.range W) (fun w hw=>hs w (Finset.mem_range.mp hw))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh
end
open scoped BigOperators Classical
open Filter
lemma wO:∃ a δ t:ℝ,∃ K:ℕ,
    0<a ∧ a≤1 ∧ 2*a≤δ ∧ 0<t ∧ 0<K ∧
    a≤(2:ℝ)^K*cZ a ∧
    4*Real.log 4/((2:ℝ)^K-1)≤(cZ a/4)/10000 ∧
    ∀ᶠ X:ℝ in atTop,∃ J:Finset ℕ,
      t*X≤J.card ∧ (∀ i∈J,∀ j∈J,i<j → i+K≤j) ∧
      ∀ j∈J,X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card:=by
  obtain ⟨c,δ,hc,hδ,he⟩:=dS.nF
  let a:=min (δ/4) 1
  have ha:0<a:=lt_min (by positivity) (by norm_num)
  have ha1:a≤1:=min_le_right _ _
  have KI:2*a≤δ:=by have:=min_le_left (δ/4) 1; dsimp only [a]; linarith only [this,hδ]
  have hv:0<cZ a:=jZ ha
  have Wr:=tendsto_pow_atTop_atTop_of_one_lt (by norm_num:(1:ℝ)<2)
  have hn:=Wr.eventually (eventually_ge_atTop (max (a/cZ a) (1+160000*Real.log 4/cZ a)))
  obtain ⟨K,hK,hpow⟩:=(eventually_gt_atTop 0 |>.and hn).exists
  have hlo:=(le_max_left _ _).trans hpow
  have hhi:=(le_max_right _ _).trans hpow
  have jI:a≤(2:ℝ)^K*cZ a:=(div_le_iff₀ hv).mp hlo
  have hden:0<(2:ℝ)^K-1:=by
    have:=one_lt_pow₀ (by norm_num:(1:ℝ)<2) (by omega:K≠0)
    linarith only [this]
  have jz:4*Real.log 4/((2:ℝ)^K-1)≤(cZ a/4)/10000:=by
    have hh:160000*Real.log 4≤((2:ℝ)^K-1)*cZ a:=by
      apply (div_le_iff₀ hv).mp
      linarith only [hhi]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hh]
  refine ⟨a,δ,c/K,K,ha,ha1,KI,div_pos hc (by exact_mod_cast hK),hK,jI,jz,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩:=hX
  obtain ⟨b,_,hcard,hsep⟩:=O6 J hK
  refine ⟨J.filter (fun j=>j%K=b),?_,hsep,?_⟩
  · have hh:=(div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
open Filter
lemma uq {m W:ℕ} (J:ℕ → Finset ℕ)
    (hb:∀ w<W,∀ j∈J w,j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m))
    {j:ℕ} (hj:j∈jN W J) :
    (2:ℝ)^j≤Real.exp (21/20*(100:ℝ)^W*Real.exp m):=by
  obtain ⟨w,hw,hj⟩:=Finset.mem_biUnion.mp hj
  have hw':=Finset.mem_range.mp hw
  have hp:=mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
  rw [←Real.exp_log (by positivity:(0:ℝ)<2^j),Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith only [hb w hw' j hj,hp]
lemma zS (W:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀ J:ℕ → Finset ℕ,
      (∀ w<W,∀ j∈J w,j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      c8 ((jN W J).biUnion (fun j=>(cP j).e6))≤
        Real.exp ((2*(100:ℝ)^W)*Real.exp m):=by
  have hp:=fD (4*Real.log 4*(3*(W:ℝ)*(100:ℝ)^W))
    (a:=(19/20)*(100:ℝ)^W) (by positivity) 1
  have ht:Tendsto (fun m:ℕ=>Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hp,ht.eventually (eventually_ge_atTop (2:ℝ))] with m hp hm
  intro J hJ
  have he:=fun (j:ℕ) (hj:j∈jN W J)=>uq J hJ hj
  have hcard:=wN J hm hJ
  have hs:(∑ j∈jN W J,c8 (cP j).e6)≤
      (4*Real.log 4)*((jN W J).card:ℝ)*Real.exp (21/20*(100:ℝ)^W*Real.exp m):=by
    calc
      _ ≤ ∑ _j∈jN W J,(4*Real.log 4)*Real.exp (21/20*(100:ℝ)^W*Real.exp m):=by
        apply Finset.sum_le_sum
        intro j hj
        exact (nC j).trans
          (mul_le_mul_of_nonneg_left (he j hj) (by positivity))
      _ = _:=by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hcard':=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard (show 0≤4*Real.log 4 by positivity))
    (Real.exp_nonneg (21/20*(100:ℝ)^W*Real.exp m))
  have hh:=mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (21/20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hh
  simp only [pow_one] at hh
  have heq:(19/20)*100^W*Real.exp (m:ℝ)+21/20*100^W*Real.exp m=
      (2*(100:ℝ)^W)*Real.exp m:=by ring
  rw [heq] at hh
  apply (oZ _ _).trans (hs.trans (hcard'.trans _))
  convert hh using 1; ring
theorem vF (D:ℝ) (W:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀ J:ℕ → Finset ℕ,
      (∀ w<W,∀ j∈J w,j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      (∀ i∈jN W J,∀ j∈jN W J,∀ a<cE j,
        2*Real.binEntropy ((a:ℝ)/(d5 W m+1))+
          ((a:ℝ)/(d5 W m+1))*((cE i:ℝ)*Real.log (bY D).card+
            2*c8 ((jN W J).biUnion (fun j=>(cP j).e6)))≤
          Real.exp (-Real.exp m)) ∧
      ((jN W J).card:ℝ)*Real.exp (-Real.exp m)≤1:=by
  have hA:1≤2*(100:ℝ)^W:=by have:=jV W; linarith only [this]
  have ht:Tendsto (fun m:ℕ=>Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [zS W,
    ht.eventually (xO (H:=Real.log (bY D).card) hA),
    ht.eventually (xP (3*(W:ℝ)*(100:ℝ)^W)),
    ht.eventually (eventually_ge_atTop (2:ℝ))] with m Vh hsmooth Aa hm
  intro J hJ
  have hL (j:ℕ) (hj:j∈jN W J) :
      (cE j:ℝ)≤Real.exp ((2*(100:ℝ)^W)*Real.exp m):=by
    apply (o7 j).trans ((uq J hJ hj).trans _)
    apply Real.exp_le_exp.mpr
    have:0≤(100:ℝ)^W*Real.exp m:=by positivity
    nlinarith only [this]
  constructor
  · intro i hi j hj a ha
    apply hsmooth _ _ _ _ (Nat.cast_nonneg _)
      ((show (a:ℝ)≤cE j by exact_mod_cast ha.le).trans (hL j hj))
      (Nat.cast_nonneg _) (hL i hi) (Vh J hJ)
    convert (kP W m).1 using 1
    congr 1
    ring
  · exact (mul_le_mul_of_nonneg_right (wN J hm hJ)
      (Real.exp_nonneg _)).trans Aa
end GaussianMoat
end OAI
end
section
namespace OAI
namespace GaussianMoat
open scoped BigOperators Classical
open Filter
theorem CJ (D:ℝ) (hD:1≤D):Nonempty (g3 D):=by
  obtain ⟨a,δ,t,K,ha,ha1,KI,ht,hK,jI,jz,hdensity⟩:=wO
  let c:=cZ a/4
  have hc:0<c:=div_pos (jZ ha) (by norm_num)
  let rate:=c*t/10500000
  have N9:0<rate:=by dsimp only [rate]; positivity
  obtain ⟨W,hW⟩:=exists_nat_gt (max 0 ((Real.log (bY D).card+1)/rate))
  have VK:0<W:=by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hW)
  have Ws:Real.log (bY D).card+1<(W:ℝ)*rate :=
    (div_lt_iff₀ N9).mp ((le_max_right _ _).trans_lt hW)
  have QS:∀ᶠ m:ℕ in atTop,∀ w∈Finset.range W,∀ J:ℕ → Finset ℕ,
      (∀ i<W,∀ j∈J i,((100:ℝ)^i*Real.exp m)≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card) →
      (∀ i∈J w,∀ j∈J w,i<j → i+K≤j) →
      ∀ j∈J w,∀ E:ℝ,E≤c*(2:ℝ)^j/10000 →
        Nonempty (kL D (g6 a m W J) (d5 W m)
          (cP j) (cE j) E (c/(10000000*Real.log ((2:ℝ)^j)))):=by
    apply (Finset.eventually_all (Finset.range W)).mpr
    intro w hw
    exact CH hD ha ha1 KI jI W w (Finset.mem_range.mp hw)
  obtain ⟨X0,hX0⟩:=eventually_atTop.mp hdensity
  have hexp:Tendsto (fun m:ℕ=>Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨m,QS,hsmooth,hm⟩ :=
    (QS.and ((vF D W).and
      (hexp.eventually (eventually_ge_atTop (max X0 (K*Real.log 2)))))).exists
  have hmX:X0≤Real.exp (m:ℝ):=(le_max_left _ _).trans hm
  have Y7:K*Real.log 2≤Real.exp (m:ℝ):=(le_max_right _ _).trans hm
  have Ud:∀ w:ℕ,∃ J:Finset ℕ,
      t*((100:ℝ)^w*Real.exp m)≤J.card ∧
      (∀ i∈J,∀ j∈J,i<j → i+K≤j) ∧
      ∀ j∈J,(100:ℝ)^w*Real.exp m≤j*Real.log 2 ∧
        j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dS.d6 j).card:=by
    intro w
    apply hX0 _ (hmX.trans _)
    have:=jV w
    nlinarith only [this,Real.exp_pos (m:ℝ)]
  choose J hdense hsep hbounds using Ud
  let U:=jN W J
  have hJ:∀ w<W,∀ j∈J w,(100:ℝ)^w*Real.exp m≤j*Real.log 2 ∧
      j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m):=by
    intro w _ j hj; exact ⟨(hbounds w j hj).1,(hbounds w j hj).2.1⟩
  have hU:U.Nonempty:=by
    have Wt:0<(J 0).card:=by
      have hpos:0<t*((100:ℝ)^0*Real.exp m):=by positivity
      exact_mod_cast hpos.trans_le (hdense 0)
    obtain ⟨j,hj⟩:=Finset.card_pos.mp Wt
    exact ⟨j,Finset.mem_biUnion.mpr ⟨0,Finset.mem_range.mpr VK,hj⟩⟩
  have hUcard:0<U.card:=Finset.card_pos.mpr hU
  have Tj:U.card-1+1=U.card:=by omega
  have Xt:=Lz J (Real.exp_pos (m:ℝ)) Y7 hJ (fun w _=>hsep w)
  obtain ⟨hsmooth,Aa⟩:=hsmooth J (fun w hw j hj=>(hJ w hw j hj).2)
  refine ⟨{
    schedule:=g6 a m W J
    smoothing:=d5 W m
    batches:=jw U
    last:=U.card-1
    lengths:=fun n=>cE (jw U n)
    rates:=fun n=>c/(10000000*Real.log ((2:ℝ)^(jw U n)))
    error:=Real.exp (-Real.exp m)
    batch:=?_
    divides:=?_
    nonneg:=(Real.exp_pos _).le
    smooth:=?_
    excess:=?_
  }⟩
  · intro n hn
    apply Classical.choice
    have hn':n<U.card:=by omega
    have hmem:=mC U hn'
    obtain ⟨w,hw,Y8⟩:=Finset.mem_biUnion.mp hmem
    apply (QS w hw J (fun w _=>hbounds w) (hsep w) _ Y8 _)
    have hh:=xQ U hK hn' Xt
    have hm:=mul_le_mul_of_nonneg_right jz (show (0:ℝ)≤2^(jw U n) by positivity)
    exact hh.trans (by convert hm using 1; ring)
  · intro n hn
    exact Jx (l9 U (Nat.lt_succ_self n) (by omega)).le
  · intro n hn a ha'
    rw [Tj,zR]
    exact hsmooth _ (mC U (by omega)) _ (mC U (by omega)) a ha'
  · rw [Tj,Rq U (fun j=>c/(10000000*Real.log ((2:ℝ)^j)))]
    have hsum:=QO J (Real.exp_pos (m:ℝ)) hc hJ (fun w _=>hdense w)
    have Wv:((U.card-1:ℕ):ℝ)*Real.exp (-Real.exp m)≤1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le U.card 1:((U.card-1:ℕ):ℝ)≤U.card)
        (Real.exp_nonneg _)).trans Aa
    have hh:=Ws.trans_le hsum
    linarith only [Wv,hh]
theorem xT:kD :=
  wI CJ
theorem fullMain:MainEndpoint ∧ CQ :=
  z4 xT
end GaussianMoat
end OAI
end

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_gaussian_moat_problem.main) := by
  rintro ⟨f, B, hinj, hprime, hB⟩
  have h : OAI.GaussianMoat.MainEndpoint := OAI.GaussianMoat.fullMain.1
  unfold OAI.GaussianMoat.MainEndpoint at h
  exact h B f (fun t => (hprime t).irreducible) hinj (fun t => by rw [dist_eq_norm]; exact hB t)
