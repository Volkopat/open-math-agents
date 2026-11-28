import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1

/-! Erdős and Selfridge (1975), Section 2.1. For each integer take its largest divisor from the indicated finite smooth set. A prime dividing the complementary factor forces a lower bound on this divisor. The remaining cardinality estimates follow from explicit periodic counts. -/

namespace Coeff930

def tally (P : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => tally P n + (P (n+1)).toNat

def scan (P : ℕ → Bool) (d c err : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, t, a => decide (d*a ≤ c*t+err)
  | n+1, t, a => decide (d*a ≤ c*t+err) && scan P d c err n (t+1) (a+(P (t+1)).toNat)

theorem scanSound (P : ℕ → Bool) (d c e n t : ℕ)
    (h : scan P d c e n t (tally P t)) {r : ℕ} (hlo : t ≤ r) (hhi : r ≤ t+n) :
    d*tally P r ≤ c*r+e := by
  induction n generalizing t with
  | zero =>
    have hr : r=t := by omega
    simpa [scan,hr] using h
  | succ n ih =>
    have hh := Bool.and_eq_true_iff.mp h
    rcases eq_or_lt_of_le hlo with hr|hr
    · simpa [hr] using hh.1
    · exact ih (t+1) hh.2 (by omega) (by omega)

theorem wheelBound (P : ℕ → Bool) (m d c e : ℕ) (hm : 0 < m)
    (hper : ∀ n, P (n+m)=P n)
    (hblock : d*tally P m ≤ c*m)
    (hscan : scan P d c e m 0 0) (n : ℕ) :
    d*tally P n ≤ c*n+e := by
  have shift (r : ℕ) : tally P (r+m) = tally P r + tally P m := by
    induction r with
    | zero => simp [tally]
    | succ r ih =>
      rw [show r+1+m=(r+m)+1 by omega, tally, ih,
        show r+m+1=(r+1)+m by omega, hper, tally]
      omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ m
    · exact scanSound P d c e m 0 hscan (Nat.zero_le _) (by omega)
    · have prev := ih (n-m) (by omega)
      have he : (n-m)+m=n := by omega
      have hs := shift (n-m)
      rw [he] at hs
      rw [hs,Nat.mul_add]
      calc _ ≤ c*(n-m)+e+c*m := Nat.add_le_add prev hblock
        _ = _ := by have := congrArg (c*·) he; simp only [Nat.mul_add] at this; omega

open Finset

def wheelPart (P : ℕ → Bool) (b : ℕ) : Finset ℕ := ((range b).filter (fun t => P (t+1))).image (·+1)

theorem wheelPart_card (P : ℕ → Bool) (b : ℕ) : (wheelPart P b).card = tally P b := by
  rw [wheelPart, card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]
  induction b with
  | zero => simp [tally]
  | succ n ih =>
    rw [range_add_one, filter_insert]
    cases h : P (n+1) <;> simp [h,tally,ih]

theorem mem_wheelPart {P : ℕ → Bool} {n b : ℕ} (hn : 0<n) (hb : n≤b) (h : P n) :
    n ∈ wheelPart P b := by
  refine mem_image.mpr ⟨n-1,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,by omega⟩
  simpa [show n-1+1=n by omega] using h

theorem bound (P : ℕ → Bool) (m d c e : ℕ) (hm : 0 < m) (hper : ∀ n, P (n+m)=P n)
    (hblock : d*tally P m ≤ c*m) (hscan : scan P d c e m 0 0) (n : ℕ) :
    d*(wheelPart P n).card ≤ c*n+e :=
  wheelPart_card P n ▸ wheelBound P m d c e hm hper hblock hscan n

def prLeast2 (n : ℕ) : Bool := decide (n%2 = 0)
def prLeast3 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 = 0)
def prLeast5 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 = 0)
def prLeast7 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 = 0)
def prFree210 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 ≠ 0)
def prLeast11 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 ≠ 0 ∧ n%11 = 0)
def prFree2310 (n : ℕ) : Bool := decide (n%2 ≠ 0 ∧ n%3 ≠ 0 ∧ n%5 ≠ 0 ∧ n%7 ≠ 0 ∧ n%11 ≠ 0)

def b2 := bound prLeast2 2 2 1 0 (by decide) (by simp [prLeast2, Nat.add_mod])
  (by decide +kernel) (by decide +kernel)
def b3 := bound prLeast3 6 6 1 3 (by decide) (by simp [prLeast3, Nat.add_mod])
  (by decide +kernel) (by decide +kernel)
def b5 := bound prLeast5 30 30 2 20 (by decide) (by simp [prLeast5, Nat.add_mod])
  (by decide +kernel) (by decide +kernel)
def b7 := bound prLeast7 210 210 8 196 (by decide) (by simp [prLeast7, Nat.add_mod])
  (by decide +kernel) (by decide +kernel)
def f210 := bound prFree210 210 210 48 318 (by decide) (by simp [prFree210, Nat.add_mod])
  (by decide +kernel) (by decide +kernel)
def b11 := bound prLeast11 2310 2310 48 3498 (by decide) (by simp [prLeast11, Nat.add_mod])
  (by decide +kernel) (by decide +kernel)
def f2310 := bound prFree2310 2310 2310 480 5820 (by decide)
  (by simp [prFree2310, Nat.add_mod]) (by decide +kernel) (by decide +kernel)

theorem maxFactor {V : Finset ℕ} (h1 : 1 ∈ V) {s : ℕ} (hs : 0<s) :
    ∃ u v : ℕ, 0<u ∧ 0<v ∧ v ∈ V ∧ s=u*v ∧
      ∀ p : ℕ, 1<p → p ∣ u → p*v ∉ V := by
  classical
  let D := V.filter (· ∣ s)
  have hD : D.Nonempty := ⟨1,mem_filter.mpr ⟨h1,one_dvd _⟩⟩
  have hv := mem_filter.mp (D.max'_mem hD)
  obtain ⟨u,hu⟩ := hv.2
  have hval : s=u*D.max' hD := hu.trans (Nat.mul_comm _ _)
  have hpos : 0 < u*D.max' hD := hval ▸ hs
  refine ⟨u,_,Nat.pos_of_mul_pos_right hpos,Nat.pos_of_mul_pos_left hpos,hv.1,hval,
    fun p hp hd hmem => ?_⟩
  have hl := D.le_max' (p*_) (mem_filter.mpr ⟨hmem,hval ▸ mul_dvd_mul hd (dvd_refl _)⟩)
  have := Nat.mul_lt_mul_of_pos_right hp (Nat.pos_of_mul_pos_left hpos)
  omega

/-- If the prime `p` divides `u`, maximality of `v` forces `v ≥ c`, so `u ≤ x / c`. -/
theorem br {V : Finset ℕ} {P : ℕ → Bool} {u v x : ℕ} (c p : ℕ) (hc : 0 < c) (hp : 1 < p)
    (hcl : ∀ v ∈ V, v < c → p*v ∈ V) (hu : 0<u) (hup : u*v ≤ x)
    (hmax : ∀ p : ℕ, 1<p → p ∣ u → p*v ∉ V) (hV : v ∈ V) (hd : u%p=0) (hP : P u) :
    u ∈ wheelPart P (x/c) := by
  have hh : c ≤ v := by
    by_contra! hlt
    exact hmax p hp (Nat.dvd_of_mod_eq_zero hd) (hcl v hV hlt)
  exact mem_wheelPart hu ((Nat.le_div_iff_mul_le hc).mpr ((Nat.mul_le_mul_left u hh).trans hup)) hP

private def VA : Finset ℕ := ([1,2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,21,24,25,27,28,30,32,35,36] : List ℕ).toFinset

private def UA (x : ℕ) := wheelPart prLeast2 (x/20) ∪ wheelPart prLeast3 (x/14) ∪ wheelPart prLeast5 (x/8) ∪ wheelPart prLeast7 (x/6) ∪ wheelPart prFree210 x

theorem coverA (x s : ℕ) (hs : 0 < s) (hx : s ≤ x) : ∃ u ∈ UA x, ∃ v ∈ VA, s=u*v := by
  obtain ⟨u,v,hu,hv,hV,he,hmax⟩ := maxFactor (V := VA) (by decide) hs
  refine ⟨u, ?_, v,hV,he⟩
  have hup : u*v ≤ x := he ▸ hx
  simp only [UA,Finset.mem_union]
  by_cases h2 : u%2=0
  · have := br 20 2 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h2 (P := prLeast2) (by simp [prLeast2,h2])
    tauto
  by_cases h3 : u%3=0
  · have := br 14 3 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h3 (P := prLeast3) (by simp [prLeast3,h2,h3])
    tauto
  by_cases h5 : u%5=0
  · have := br 8 5 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h5 (P := prLeast5) (by simp [prLeast5,h2,h3,h5])
    tauto
  by_cases h7 : u%7=0
  · have := br 6 7 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h7 (P := prLeast7) (by simp [prLeast7,h2,h3,h5,h7])
    tauto
  have := mem_wheelPart (P := prFree210) hu (by simpa using (Nat.le_mul_of_pos_right u hv).trans hup) (by simp [prFree210,h2,h3,h5,h7])
  tauto

theorem sizeA (x : ℕ) : 1260 * (UA x).card ≤ 353*x+5040 := by
  have := b2 (x/20)
  have := b3 (x/14)
  have := b5 (x/8)
  have := b7 (x/6)
  have := f210 x
  have : (UA x).card ≤ (wheelPart prLeast2 (x/20)).card + (wheelPart prLeast3 (x/14)).card + (wheelPart prLeast5 (x/8)).card + (wheelPart prLeast7 (x/6)).card + (wheelPart prFree210 x).card :=
    (card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _)) _)
  omega

private def VB : Finset ℕ := ([1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,20,21,22,24,25,27,28,30,32,33,35,36,40,42,44,45,48,49,50,54,55,56,60,63,64,66,70,72,75,77,80,81,84,88,90,96,98,99,100] : List ℕ).toFinset

private def UB (x : ℕ) := wheelPart prLeast2 (x/54) ∪ wheelPart prLeast3 (x/35) ∪ wheelPart prLeast5 (x/21) ∪ wheelPart prLeast7 (x/15) ∪ wheelPart prLeast11 (x/10) ∪ wheelPart prFree2310 x

theorem coverB (x s : ℕ) (hs : 0 < s) (hx : s ≤ x) : ∃ u ∈ UB x, ∃ v ∈ VB, s=u*v := by
  obtain ⟨u,v,hu,hv,hV,he,hmax⟩ := maxFactor (V := VB) (by decide) hs
  refine ⟨u, ?_, v,hV,he⟩
  have hup : u*v ≤ x := he ▸ hx
  simp only [UB,Finset.mem_union]
  by_cases h2 : u%2=0
  · have := br 54 2 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h2 (P := prLeast2) (by simp [prLeast2,h2])
    tauto
  by_cases h3 : u%3=0
  · have := br 35 3 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h3 (P := prLeast3) (by simp [prLeast3,h2,h3])
    tauto
  by_cases h5 : u%5=0
  · have := br 21 5 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h5 (P := prLeast5) (by simp [prLeast5,h2,h3,h5])
    tauto
  by_cases h7 : u%7=0
  · have := br 15 7 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h7 (P := prLeast7) (by simp [prLeast7,h2,h3,h5,h7])
    tauto
  by_cases h11 : u%11=0
  · have := br 10 11 (by decide) (by decide) (by decide +kernel) hu hup hmax hV h11 (P := prLeast11) (by simp [prLeast11,h2,h3,h5,h7,h11])
    tauto
  have := mem_wheelPart (P := prFree2310) hu (by simpa using (Nat.le_mul_of_pos_right u hv).trans hup) (by simp [prFree2310,h2,h3,h5,h7,h11])
  tauto

theorem sizeB (x : ℕ) : 41580 * (UB x).card ≤ 9547*x+291060 := by
  have := b2 (x/54)
  have := b3 (x/35)
  have := b5 (x/21)
  have := b7 (x/15)
  have := b11 (x/10)
  have := f2310 x
  have : (UB x).card ≤ (wheelPart prLeast2 (x/54)).card + (wheelPart prLeast3 (x/35)).card + (wheelPart prLeast5 (x/21)).card + (wheelPart prLeast7 (x/15)).card + (wheelPart prLeast11 (x/10)).card + (wheelPart prFree2310 x).card :=
    (card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _)) _)) _)
  omega

end Coeff930

open Coeff930

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1.H1 := by
  intro x
  constructor
  · refine ⟨UA x,VA,coverA x,?_⟩
    have hc : VA.card.choose 2 = 300 := by decide +kernel
    have := sizeA x
    omega
  · refine ⟨UB x,VB,coverB x,?_⟩
    have hc : VB.card.choose 2 = 1485 := by decide +kernel
    have := sizeB x
    omega

