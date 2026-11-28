import OMAStatements.S_oeis_a230312


namespace OMA.S_oeis_a230312
def z (n : ℕ) : GaussianInt := ⟨2*n,1⟩
def N (n : ℕ) := 4*n^2+1

theorem z_norm (n : ℕ) : (z n).norm = (N n : ℤ) := by
  simp [z,N,Zsqrtd.norm]
  ring

theorem z_norm_product (n : ℕ) : z n * star (z n) = (N n : GaussianInt) := by
  simpa [z_norm] using (Zsqrtd.norm_eq_mul_conj (n:=z n)).symm

private theorem z_cast_dvd {n t : ℕ} (h : z n ∣ (t : GaussianInt)) : N n ∣ t := by
  obtain ⟨⟨a,b⟩,he⟩ := h
  have hr := congrArg Zsqrtd.re he
  have hi := congrArg Zsqrtd.im he
  simp [z] at hr hi
  zify
  refine ⟨-b,?_⟩
  push_cast [N]
  linear_combination hr - (2*(n:ℤ))*hi

private theorem z_not_unit {n : ℕ} (hn : 0<n) : ¬IsUnit (z n) := by
  intro h
  have hh := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ)≤0) _).mpr h
  rw [z_norm] at hh
  simp [N] at hh
  omega

theorem norm_prime_iff {n : ℕ} (hn : 0<n) : (N n).Prime ↔ Irreducible (z n) := by
  constructor
  · intro hp
    refine ⟨z_not_unit hn,?_⟩
    intro a b hab
    have he := congrArg (fun w : GaussianInt => w.norm.natAbs) hab
    rw [z_norm, Zsqrtd.norm_mul, Int.natAbs_mul] at he
    simp only [Int.natAbs_natCast] at he
    rcases (Nat.dvd_prime hp).mp (he ▸ dvd_mul_right a.norm.natAbs b.norm.natAbs) with ha|ha
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
    · have ha0 : 0<a.norm.natAbs := ha ▸ hp.pos
      have hb : b.norm.natAbs=1 := by
        apply Nat.eq_of_mul_eq_mul_left ha0
        rw [mul_one, ←he, ha]
      exact Or.inr (Zsqrtd.norm_eq_one_iff.mp hb)
  · intro hi
    have hp := hi.prime
    have hN : 2 ≤ N n := by dsimp [N]; nlinarith
    refine Nat.prime_def_lt'.mpr ⟨hN,?_⟩
    intro d hd hdn hdiv
    obtain ⟨e,hef⟩ := hdiv
    have hw : z n ∣ (d : GaussianInt)*e := by
      rw [← Nat.cast_mul, ← hef, ← z_norm_product]
      exact dvd_mul_right _ _
    rcases hp.dvd_or_dvd hw with hh|hh
    · have hle := Nat.le_of_dvd (by omega : 0<d) (z_cast_dvd hh)
      omega
    · have he0 : 0<e := by
        by_contra! hc
        have hez : e=0 := by omega
        rw [hez,mul_zero] at hef
        omega
      have hle := Nat.le_of_dvd he0 (z_cast_dvd hh)
      nlinarith

theorem z_coprime (n : ℕ) : IsCoprime (z n) (star (z n)) := by
  refine ⟨(⟨n,-1⟩ : GaussianInt),(⟨-(n:ℤ),0⟩ : GaussianInt),?_⟩
  ext <;> simp [z] <;> ring

theorem norm_flip {a b : GaussianInt} : (a*star b).norm = (a*b).norm := by simp

theorem nontrivial_flip {n : ℕ} {a b : GaussianInt} (hz : z n = a*b)
    (hau : ¬IsUnit a) (hbu : ¬IsUnit b) :
    ¬ z n ∣ a*star b ∧ ¬ z n ∣ star (a*star b) := by
  have ca := z_coprime n
  rw [hz, star_mul] at ca
  have ha0 : a≠0 := by
    intro h
    have he := congrArg Zsqrtd.im hz
    simp [h,z] at he
  have hb0 : b≠0 := by
    intro h
    have he := congrArg Zsqrtd.im hz
    simp [h,z] at he
  constructor
  · rintro ⟨c,hc⟩
    rw [hz, mul_assoc] at hc
    have he : star b=b*c := mul_left_cancel₀ ha0 hc
    exact hbu (ca.isUnit_of_dvd' (dvd_mul_left _ _) ((Dvd.intro c he.symm).trans (dvd_mul_right _ _)))
  · rintro ⟨c,hc⟩
    rw [hz, star_mul, star_star] at hc
    have he : star a=a*c := by
      apply (mul_left_cancel₀ hb0)
      linear_combination hc
    exact hau (ca.isUnit_of_dvd' (dvd_mul_right _ _) ((Dvd.intro c he.symm).trans (dvd_mul_left _ _)))

end OMA.S_oeis_a230312
namespace OMA.S_oeis_a230312

def obvious (w : GaussianInt) := w.re=1 ∨ w.re= -1 ∨ w.im=1 ∨ w.im= -1

private theorem imag_from_real {r s : ℤ} {n : ℕ} (h : r^2+s^2=4*(n:ℤ)^2+1) (hr : r=1 ∨ r= -1) :
    s=2*n ∨ s= -(2*(n:ℤ)) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rcases hr with rfl|rfl <;> nlinarith

/-- A Gaussian number with the given norm and a unit coordinate is a unit multiple
of the distinguished number or its conjugate. -/
theorem obvious_dvd {n : ℕ} {w : GaussianInt} (hn : w.norm=(z n).norm) (hw : obvious w) :
    z n ∣ w ∨ z n ∣ star w := by
  obtain ⟨r,s⟩ := w
  have he : r^2+s^2=4*(n:ℤ)^2+1 := by
    rw [z_norm] at hn
    simp [Zsqrtd.norm,N] at hn
    nlinarith
  change r=1 ∨ r= -1 ∨ s=1 ∨ s= -1 at hw
  have he' : s^2+r^2=4*(n:ℤ)^2+1 := by linarith
  rcases hw with hr|hr|hs|hs
  · rcases imag_from_real he (Or.inl hr) with hs|hs <;> subst r <;> subst s
    · exact Or.inr ⟨⟨0,-1⟩,by ext <;> simp [z]⟩
    · exact Or.inl ⟨⟨0,-1⟩,by ext <;> simp [z]⟩
  · rcases imag_from_real he (Or.inr hr) with hs|hs <;> subst r <;> subst s
    · exact Or.inl ⟨⟨0,1⟩,by ext <;> simp [z]⟩
    · exact Or.inr ⟨⟨0,1⟩,by ext <;> simp [z]⟩
  · rcases imag_from_real he' (Or.inl hs) with hr|hr <;> subst r <;> subst s
    · exact Or.inl (dvd_refl _)
    · exact Or.inr ⟨-1, by ext <;> simp [z]⟩
  · rcases imag_from_real he' (Or.inr hs) with hr|hr <;> subst r <;> subst s
    · exact Or.inr ⟨1, by ext <;> simp [z]⟩
    · exact Or.inl ⟨-1, by ext <;> simp [z]⟩

private theorem obvious_of_dvd {n : ℕ} {w : GaussianInt} (h : w.norm=(z n).norm) (hd : z n ∣ w) :
    obvious w := by
  obtain ⟨⟨a,b⟩,rfl⟩ := hd
  have hz : (z n).norm ≠ 0 := by rw [z_norm]; unfold N; positivity
  rw [Zsqrtd.norm_mul] at h
  have hu : (⟨a,b⟩:GaussianInt).norm = 1 := by
    apply mul_left_cancel₀ hz
    simpa using h
  change a*a - (-1)*b*b = 1 at hu
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> by_contra! hh <;> nlinarith [sq_nonneg b, sq_nonneg (a-1), sq_nonneg (a+1)]
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor <;> by_contra! hh <;> nlinarith [sq_nonneg a, sq_nonneg (b-1), sq_nonneg (b+1)]
  obtain ⟨ha,ha'⟩ := ha
  obtain ⟨hb,hb'⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num [obvious,z] at *

theorem prime_all_obvious {n : ℕ} (hn : 0<n) (hp : (N n).Prime) (w : GaussianInt)
    (hw : w.norm=(z n).norm) : obvious w := by
  have he : z n ∣ w*star w := by
    rw [← Zsqrtd.norm_eq_mul_conj,hw,Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  rcases ((norm_prime_iff hn).mp hp).prime.dvd_or_dvd he with hd|hd
  · exact obvious_of_dvd hw hd
  · have hw' : (star w).norm=w.norm := by simp [Zsqrtd.norm]
    have ho := obvious_of_dvd (hw'.trans hw) hd
    simp [obvious] at ho ⊢
    omega

end OMA.S_oeis_a230312

namespace OMA.S_oeis_a230312

private theorem no_square_between {n b : ℕ} (hn : 0<n) (h : b^2=4*n^2+1) : False := by
  by_cases hb : b≤2*n
  · have hh : b^2 ≤ (2*n)^2 := by gcongr
    nlinarith
  · have hb' : 2*n+1≤b := by omega
    have hh : (2*n+1)^2≤b^2 := by gcongr
    nlinarith

private theorem even_odd_rep {n l r : ℕ} (hn : 0<n) (h : l^2+r^2=4*n^2+1)
    (hl : l%2=0) (hr : r%2=1) (hr' : r≠1) :
    ∃ x k : ℕ, 0<x ∧ x<n ∧ n^2=x^2+k*(k+1) := by
  by_cases hl0 : l=0
  · exact False.elim (no_square_between hn (by simpa [hl0] using h))
  let x := l/2
  let k := r/2
  have hx : l=2*x := by dsimp [x]; omega
  have hk : r=2*k+1 := by dsimp [k]; omega
  have hk' : 0<k := by omega
  have he : n^2=x^2+k*(k+1) := by rw [hx,hk] at h; nlinarith only [h]
  refine ⟨x,k,by omega,?_,he⟩
  by_contra! hle
  have hp : n^2≤x^2 := by gcongr
  nlinarith

private theorem rep_of_nonobvious {n : ℕ} (hn : 0<n) {w : GaussianInt}
    (hw : w.norm=(z n).norm) (ho : ¬obvious w) :
    ∃ x k : ℕ, 0<x ∧ x<n ∧ n^2=x^2+k*(k+1) := by
  let l := w.re.natAbs
  let r := w.im.natAbs
  have he : l^2 + r^2 = 4*n^2+1 := by
    have he' := GaussianInt.natAbs_norm_eq w
    rw [hw,z_norm] at he'
    rw [Int.natAbs_natCast] at he'
    simpa [l,r,N,pow_two] using he'.symm
  have hl : l≠1 := by
    intro hh
    rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr hh) with hh|hh
    · exact ho (Or.inl hh)
    · exact ho (Or.inr (Or.inl hh))
  have hr : r≠1 := by
    intro hh
    rcases Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr hh) with hh|hh
    · exact ho (Or.inr (Or.inr (Or.inl hh)))
    · exact ho (Or.inr (Or.inr (Or.inr hh)))
  have hmod := congrArg (Nat.cast (R:=ZMod 2)) he
  push_cast at hmod
  have hf : ∀ a b c : ZMod 2, a^2+b^2=4*c^2+1 →
      (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) := by decide
  rcases hf _ _ _ hmod with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact even_odd_rep hn he (congrArg ZMod.val ha) (congrArg ZMod.val hb) hr
  · exact even_odd_rep hn (by simpa [add_comm] using he) (congrArg ZMod.val hb) (congrArg ZMod.val ha) hl

theorem classification (n : ℕ) (hn : 0<n) :
    (¬ ∃ x k : ℕ, 0<x ∧ x<n ∧ n^2=x^2+k*(k+1)) ↔ (4*n^2+1).Prime := by
  constructor
  · intro h
    by_contra hp
    have hni := mt (norm_prime_iff hn).mpr hp
    have hnu : ¬IsUnit (z n) := by
      intro hu
      have hh := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ)≤0) _).mpr hu
      rw [z_norm] at hh
      simp [N] at hh
      omega
    obtain ⟨a,b,hz,hau,hbu⟩ : ∃ a b : GaussianInt, z n=a*b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
      simpa [irreducible_iff,hnu,not_forall,not_or] using hni
    have he : (a*star b).norm = (z n).norm := by rw [hz,norm_flip]
    apply h (rep_of_nonobvious hn he ?_)
    intro ho
    exact (not_or.mpr (nontrivial_flip hz hau hbu)) (obvious_dvd he ho)
  · rintro hp ⟨x,k,hx,hxn,he⟩
    let w : GaussianInt := ⟨2*x, 2*k+1⟩
    have he' : (n:ℤ)^2=(x:ℤ)^2+(k:ℤ)*(k+1) := by exact_mod_cast he
    have hnorm : w.norm=(z n).norm := by rw [z_norm]; simp [N,w,Zsqrtd.norm]; nlinarith only [he']
    have hobs := prime_all_obvious hn hp w hnorm
    have hk : k≠0 := by
      rintro rfl
      simp at he
      omega
    change (2*(x:ℤ)=1 ∨ 2*(x:ℤ)= -1 ∨ 2*(k:ℤ)+1=1 ∨ 2*(k:ℤ)+1= -1) at hobs
    omega

end OMA.S_oeis_a230312

theorem OMA.solution : type_of% @OMA.S_oeis_a230312.main := OMA.S_oeis_a230312.classification
