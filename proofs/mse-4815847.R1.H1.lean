import OMAReductions.R_mse_4815847_R1

-- Credit: @YOHSUKE-TAKAHASHI
/-!
For each cone of directions, a pivot certifies that both closed half-planes
through it contain more than half of the total weight. Both cone endpoints
are checked. Row reflection and exchange of sides cover the other directions.
The certificates encode only pivot runs and exceptions. Every majority
inequality and the entire cover are checked in the kernel.
-/
namespace PascalCut

open Finset OMA.S_mse_4815847

def mass (n : ℕ) (u v d : ℤ) : ℕ :=
  ∑ p ∈ (entries n).filter (fun p => u*(p.1:ℤ)+v*p.2 ≤ d), Nat.choose p.1 p.2

def total (n : ℕ) := 2^(n+1) - 2*(n+1)

def row (r : ℕ) (u v d : ℤ) : ℕ :=
  ∑ k ∈ Ioc 0 (r-1), if u*(r:ℤ)+v*k ≤ d then Nat.choose r k else 0

theorem mass_rows (n : ℕ) (u v d : ℤ) :
    mass n u v d = ∑ r ∈ range (n+1), row r u v d := by
  unfold mass entries row
  rw [sum_filter, sum_filter, sum_product]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  have he : ((range (n+1)).filter (fun k => 1 ≤ k ∧ k+1 ≤ r)) = Ioc 0 (r-1) := by
    ext k
    simp only [mem_filter, mem_range, mem_Ioc]
    omega
  rw [← he, sum_filter]

theorem mass_zero (u v d : ℤ) : mass 0 u v d = 0 := by simp [mass, entries]

theorem mass_succ (n : ℕ) (u v d : ℤ) :
    mass (n+1) u v d = mass n u v d + row (n+1) u v d := by
  simp only [mass_rows, sum_range_succ _ (n+1)]

def rowPrefix (r k : ℕ) := ∑ x ∈ Ioc 0 k, r.choose x

theorem rowPrefix_zero (r : ℕ) : rowPrefix r 0 = 0 := by simp [rowPrefix]
theorem rowPrefix_step (r k : ℕ) : rowPrefix r (k+1) = rowPrefix r k + r.choose (k+1) := by
  exact sum_Ioc_succ_top (a := 0) (b := k) (by omega) _

theorem full_row (n : ℕ) : rowPrefix (n+1) n + 2 = 2^(n+1) := by
  have h := Nat.sum_range_choose (n+1)
  rw [sum_range_succ] at h
  have hh : ∑ x ∈ range (n+1), (n+1).choose x = 1 + rowPrefix (n+1) n := by
    have he : range (n+1) = insert 0 (Ioc 0 n) := by ext x; simp
    rw [he,
      sum_insert (by simp), Nat.choose_zero_right, rowPrefix]
  rw [hh,Nat.choose_self] at h
  omega

theorem total_eq (n : ℕ) : mass n 0 0 0 = total n := by
  induction n with
  | zero => simp [mass_zero,total]
  | succ n ih =>
    rw [mass_succ, ih]
    have h : row (n+1) 0 0 0 = rowPrefix (n+1) n := by simp [row,rowPrefix]
    rw [h]
    have h₁ := full_row n
    have h₂ : n+1 ≤ 2^n := Nat.lt_two_pow_self (n := n)
    unfold total
    rw [pow_succ 2 (n+1),pow_succ 2 n]
    omega

theorem complement (n : ℕ) (u v d : ℤ) :
    mass n u v d + mass n (-u) (-v) (-d-1) = total n := by
  rw [← total_eq, mass_rows, mass_rows, mass_rows, ← sum_add_distrib]
  refine sum_congr rfl fun r hr => ?_
  unfold row
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  simp only [neg_mul, zero_mul, zero_add, le_refl, if_true]
  split_ifs <;> omega

theorem reflect_mass (n : ℕ) (u v d : ℤ) :
    mass n (u+v) (-v) d = mass n u v d := by
  rw [mass_rows,mass_rows]
  refine sum_congr rfl fun r hr => ?_
  unfold row
  apply sum_nbij' (fun k => r-k) (fun k => r-k)
  · intro k hk
    simp only [mem_Ioc] at *
    omega
  · intro k hk
    simp only [mem_Ioc] at *
    omega
  · intro k hk
    simp only [mem_Ioc] at hk
    omega
  · intro k hk
    simp only [mem_Ioc] at hk
    omega
  · intro k hk
    simp only [mem_Ioc] at hk
    have hkr : k ≤ r := by omega
    rw [Nat.choose_symm hkr, Nat.cast_sub hkr]
    congr 1
    ring_nf

theorem rowPrefix_le_row {n k : ℕ} {u v d : ℤ} (hk : k ≤ n-1)
    (H : ∀ x, 0 < x → x ≤ k → u*(n:ℤ)+v*x ≤ d) :
    rowPrefix n k ≤ row n u v d := by
  unfold rowPrefix row
  calc
    _ = ∑ x ∈ Ioc 0 k, (if u*(n:ℤ)+v*x ≤ d then n.choose x else 0) := by
      apply sum_congr rfl
      intro x hx
      rw [if_pos (H x (mem_Ioc.mp hx).1 (mem_Ioc.mp hx).2)]
    _ ≤ _ := sum_le_sum_of_subset (fun x hx => mem_Ioc.mpr
      ⟨(mem_Ioc.mp hx).1,(mem_Ioc.mp hx).2.trans hk⟩)

end PascalCut

namespace PascalCut

def base : Nat := 2^256
def ones : Nat := (2^(256*251)-1)/(base-1)
def packed (r : Nat) := (base+1)^r * ones
def val (r k : Nat) := ((packed r >>> (256*k)) % base) - 1

def checkRow (r : Nat) : Bool :=
  val (r+1) 0 == 0 && (List.range 250).all (fun k =>
    val (r+1) (k+1) == val r k + val r (k+1) + 1)
end PascalCut

namespace PascalCut

theorem rowPrefix_pascal (r k : ℕ) :
    rowPrefix (r+1) (k+1) = rowPrefix r k + rowPrefix r (k+1) + 1 := by
  induction k with
  | zero => simp [rowPrefix_step,rowPrefix_zero,Nat.choose_succ_succ,Nat.choose_zero_right]; omega
  | succ k ih =>
    rw [rowPrefix_step (r+1) (k+1),ih,rowPrefix_step r (k+1),Nat.choose_succ_succ]
    rw [rowPrefix_step r k]
    simp only [Nat.succ_eq_add_one]
    omega

theorem valid_of_checks (h0 : (List.range 251).all (fun k => val 0 k == 0))
    (hs : ∀ r, r < 250 → checkRow r) :
    ∀ r k, r ≤ 250 → k ≤ 250 → val r k = rowPrefix r k := by
  intro r
  induction r with
  | zero =>
    intro k _ hk
    have H := List.all_eq_true.mp h0 k (List.mem_range.mpr (by omega))
    have hz : rowPrefix 0 k = 0 := by
      unfold rowPrefix
      apply Finset.sum_eq_zero
      intro x hx
      exact Nat.choose_eq_zero_of_lt (Finset.mem_Ioc.mp hx).1
    simpa [hz] using H
  | succ r ih =>
    intro k hr hk
    obtain ⟨H₁,H₂⟩ := Bool.and_eq_true_iff.mp (hs r (by omega))
    cases k with
    | zero => simpa [rowPrefix_zero] using H₁
    | succ k =>
      have H := List.all_eq_true.mp H₂ k (List.mem_range.mpr (by omega))
      simp only [beq_iff_eq] at H
      rw [H,ih k (by omega) (by omega),ih (k+1) (by omega) hk,rowPrefix_pascal]

end PascalCut

namespace PascalCut
open Finset OMA.S_mse_4815847

structure Dir where
  a : ℤ
  b : ℕ

def Dir.atPt (s : Dir) (r k : ℕ) := s.a*(r:ℤ)+(s.b:ℤ)*k
def Dir.mirror (s : Dir) : Dir := ⟨-s.a-s.b,s.b⟩
def det (l h : Dir) := h.a*l.b-l.a*h.b
def loOk (l : Dir) (u v : ℤ) := l.a*v ≤ u*l.b
def hiOk (h : Dir) (u v : ℤ) := u*h.b ≤ h.a*v

theorem between {l h : Dir} {u v X Y : ℤ}
    (hd : 0 < det l h) (hl : loOk l u v) (hh : hiOk h u v)
    (h₁ : l.a*X+(l.b:ℤ)*Y ≤ 0) (h₂ : h.a*X+(h.b:ℤ)*Y ≤ 0) :
    u*X+v*Y ≤ 0 := by
  have m₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hh) h₁
  have m₂ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) h₂
  apply nonpos_of_mul_nonpos_right _ hd
  dsimp [det]
  linarith only [m₁,m₂]

theorem location {l h : Dir} {u v : ℤ} {i j r x : ℕ}
    (hd : 0 < det l h) (hl : loOk l u v) (hh : hiOk h u v)
    (h₁ : l.atPt r x ≤ l.atPt i j) (h₂ : h.atPt r x ≤ h.atPt i j) :
    u*(r:ℤ)+v*x ≤ u*i+v*j := by
  unfold Dir.atPt at h₁ h₂
  have H := between (X := (r:ℤ)-i) (Y := (x:ℤ)-j) hd hl hh
    (by linarith only [h₁]) (by linarith only [h₂])
  linarith only [H]

def cap (s : Dir) (i j r : ℕ) : ℕ :=
  if s.b = 0 then
    if s.a*r ≤ s.a*i then r-1 else 0
  else ((s.atPt i j - s.a*r) / (s.b:ℤ)).toNat

theorem cap_safe (s : Dir) (i j r x : ℕ) (hx : 0 < x) (h : x ≤ cap s i j r) :
    s.atPt r x ≤ s.atPt i j := by
  unfold cap at h
  split at h
  next hb =>
    split at h
    next hh => simpa [Dir.atPt,hb] using hh
    next => omega
  next hb =>
    have hp : 0 < (s.b:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hb
    have he : (x:ℤ) ≤ (s.atPt i j-s.a*r)/(s.b:ℤ) := by omega
    have ht := (Int.le_ediv_iff_mul_le hp).mp he
    unfold Dir.atPt
    unfold Dir.atPt at ht
    linarith only [ht]

def roof (s : Dir) (i j r : ℕ) : Bool :=
  decide (s.a*2+s.b ≤ s.atPt i j) &&
    decide ((s.a+s.b)*r-s.b ≤ s.atPt i j)

theorem roof_safe {s : Dir} {i j r t x : ℕ} (hr : roof s i j r)
    (ht : t ≤ r) (hx : 0 < x) (hxt : x < t) : s.atPt t x ≤ s.atPt i j := by
  simp only [roof,Bool.and_eq_true,decide_eq_true_eq] at hr
  have hx' : (x:ℤ) ≤ t-1 := by omega
  have hd := mul_le_mul_of_nonneg_left hx' (Int.natCast_nonneg s.b)
  unfold Dir.atPt at hr ⊢
  by_cases h : 0 ≤ s.a+s.b
  · have he := mul_le_mul_of_nonneg_left (show (t:ℤ) ≤ r by exact_mod_cast ht) h
    linarith only [he,hd,hr.2]
  · have he := mul_le_mul_of_nonpos_left (show (2:ℤ) ≤ t by omega) (le_of_not_ge h)
    linarith only [he,hd,hr.1]

theorem roof_total {l h : Dir} {u v : ℤ} {i j r : ℕ}
    (hd : 0 < det l h) (hl : loOk l u v) (hh : hiOk h u v)
    (rl : roof l i j r) (rh : roof h i j r) :
    mass r u v (u*i+v*j) = total r := by
  rw [← total_eq]
  unfold mass
  congr 1
  ext p
  simp only [mem_filter,zero_mul,zero_add,le_refl,and_true]
  constructor
  · exact And.left
  · intro hp
    obtain ⟨⟨hp₁,hp₂⟩, hk,ht⟩ := (show (p.1 < r+1 ∧ p.2 < r+1) ∧
      1 ≤ p.2 ∧ p.2+1 ≤ p.1 by simpa [entries] using hp)
    exact ⟨hp,location hd hl hh (roof_safe rl (by omega) hk (by omega))
      (roof_safe rh (by omega) hk (by omega))⟩

def enough (l h : Dir) (i j : ℕ) : ℕ → ℕ → Bool
  | 0, need => need == 0
  | r+1, need =>
    if need = 0 then true else
    if roof l i j (r+1) && roof h i j (r+1) then decide (need ≤ total (r+1)) else
    let k := min r (min (cap l i j (r+1)) (cap h i j (r+1)))
    enough l h i j r (need-val (r+1) k)

theorem enough_sound (valid : ∀ r k, r ≤ 250 → k ≤ r → val r k = rowPrefix r k)
    {l h : Dir} {u v : ℤ} {i j : ℕ}
    (hd : 0 < det l h) (hl : loOk l u v) (hh : hiOk h u v) (r need : ℕ)
    (hr : r ≤ 250) (H : enough l h i j r need) :
    need ≤ mass r u v (u*i+v*j) := by
  induction r generalizing need with
  | zero => simp [enough] at H; omega
  | succ r ih =>
    simp only [enough] at H
    split at H
    · omega
    split at H
    next hr' =>
      obtain ⟨rl,rh⟩ := Bool.and_eq_true_iff.mp hr'
      rw [roof_total hd hl hh rl rh]
      exact of_decide_eq_true H
    next =>
      let k := min r (min (cap l i j (r+1)) (cap h i j (r+1)))
      have hk : k ≤ r := min_le_left .. 
      have HL : k ≤ cap l i j (r+1) := (min_le_right ..).trans (min_le_left ..)
      have HH : k ≤ cap h i j (r+1) := (min_le_right ..).trans (min_le_right ..)
      have ha := ih (need-val (r+1) k) (by omega) H
      rw [valid _ _ hr (by omega)] at ha
      have hb : rowPrefix (r+1) k ≤ row (r+1) u v (u*i+v*j) :=
        rowPrefix_le_row (by omega) fun x hx hxk => location hd hl hh
          (cap_safe _ _ _ _ _ hx (hxk.trans HL)) (cap_safe _ _ _ _ _ hx (hxk.trans HH))
      rw [mass_succ]
      omega

end PascalCut

namespace PascalCut

def target (n : ℕ) := total n / 2 + 1

def good (n : ℕ) (l h : Dir) (i j : ℕ) : Bool :=
  decide (0 < det l h) && decide (j ≤ i) &&
    enough l h i j n (target n) &&
    enough h.mirror l.mirror i (i-j) n (target n)

theorem mass_mono (n : ℕ) (u v : ℤ) {s t : ℤ} (hst : s ≤ t) :
    mass n u v s ≤ mass n u v t := by
  unfold mass
  apply Finset.sum_le_sum_of_subset
  intro p hp
  obtain ⟨hp,h⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp,h.trans hst⟩

theorem good_sound (valid : ∀ r k, r ≤ 250 → k ≤ r → val r k = rowPrefix r k)
    (n : ℕ) (hn : n ≤ 250) (l h : Dir) (i j : ℕ) (u v d : ℤ)
    (hl : loOk l u v) (hh : hiOk h u v) (H : good n l h i j) :
    2*mass n u v d ≠ total n := by
  simp only [good,Bool.and_eq_true,decide_eq_true_eq] at H
  obtain ⟨⟨⟨hdet,hji⟩,H₁⟩,H₂⟩ := H
  by_cases hs : u*(i:ℤ)+v*j ≤ d
  · have hle := (enough_sound valid hdet hl hh n _ hn H₁).trans (mass_mono _ _ _ hs)
    unfold target at hle
    omega
  · let u' := -u-v
    have hd' : 0 < det h.mirror l.mirror := by
      dsimp [det,Dir.mirror] at hdet ⊢
      linarith
    have hl' : loOk h.mirror u' v := by
      dsimp [hiOk,loOk,Dir.mirror,u'] at hh ⊢
      linarith
    have hh' : hiOk l.mirror u' v := by
      dsimp [hiOk,loOk,Dir.mirror,u'] at hl ⊢
      linarith
    have ht : u'*(i:ℤ)+v*((i-j:ℕ):ℤ) ≤ -d-1 := by
      rw [Nat.cast_sub hji]
      dsimp [u']
      linarith
    have hle := (enough_sound valid hd' hl' hh' n _ hn H₂).trans (mass_mono _ _ _ ht)
    have hr := reflect_mass n (-u) (-v) (-d-1)
    have hm : mass n u' v (-d-1) = mass n (-u) (-v) (-d-1) := by
      simpa [u',sub_eq_add_neg] using hr
    rw [hm] at hle
    have hc := complement n u v d
    unfold target at hle
    omega

abbrev Point := ℕ × ℕ

/-- The slope at which consecutive pivots exchange order. The last cone
ends at the horizontal normal. The subsequent check verifies each endpoint. -/
def boundary (p : Point) : List Point → Dir
  | [] => ⟨1, 0⟩
  | q :: _ => ⟨Nat.dist p.2 q.2, Nat.dist p.1 q.1⟩

def coverPoints (n : ℕ) : List Point → Dir → Bool
  | [], l => decide (l.a = 1 ∧ l.b = 0)
  | p :: ps, l =>
    let h := boundary p ps
    good n l h p.1 p.2 && coverPoints n ps h

theorem coverPoints_sound (valid : ∀ r k, r ≤ 250 → k ≤ r → val r k = rowPrefix r k)
    (n : ℕ) (hn : n ≤ 250) (ps : List Point) (l : Dir) (u v d : ℤ)
    (hl : loOk l u v) (edge : l.b = 0 → l.a*v < u*l.b) (hv : 0 ≤ v)
    (H : coverPoints n ps l) : 2*mass n u v d ≠ total n := by
  induction ps generalizing l with
  | nil =>
    obtain ⟨ha,hb⟩ := of_decide_eq_true H
    have he := edge hb
    simp [ha,hb] at he
    omega
  | cons p ps ih =>
    obtain ⟨H₁,H₂⟩ := Bool.and_eq_true_iff.mp H
    by_cases hh : hiOk (boundary p ps) u v
    · exact good_sound valid n hn _ _ _ _ u v d hl hh H₁
    · exact ih _ (le_of_not_ge hh) (fun _ => lt_of_not_ge hh) H₂

end PascalCut

namespace PascalCut

theorem solved_size (valid : ∀ r k, r ≤ 250 → k ≤ r → val r k = rowPrefix r k)
    (n : ℕ) (hn : n ≤ 250) (ps : List Point) (H : coverPoints n ps ⟨-1,2⟩)
    (u v d : ℤ) :
    (∑ p ∈ (OMA.S_mse_4815847.entries n).filter (fun p => d < u*(p.1:ℤ)+v*p.2),
      Nat.choose p.1 p.2) ≠ mass n u v d := by
  have norm (a b t : ℤ) (hb : 0 ≤ b) (ha : 0 ≤ 2*a+b) : 2*mass n a b t ≠ total n :=
    coverPoints_sound valid n hn ps ⟨-1,2⟩ a b t (by dsimp [loOk]; omega) (by simp) hb H
  have upper (a b t : ℤ) (hb : 0 ≤ b) : 2*mass n a b t ≠ total n := by
    by_cases ha : 0 ≤ 2*a+b
    · exact norm a b t hb ha
    · have h := norm (-a-b) b (-t-1) hb (by omega)
      have hr : mass n (-a-b) b (-t-1) = mass n (-a) (-b) (-t-1) := by
        simpa [sub_eq_add_neg] using reflect_mass n (-a) (-b) (-t-1)
      rw [hr] at h
      have hc := complement n a b t
      omega
  have hb : 2*mass n u v d ≠ total n := by
    by_cases hv : 0 ≤ v
    · exact upper u v d hv
    · have hu := upper (-u) (-v) (-d-1) (by omega)
      have hc := complement n u v d
      omega
  have hf : (OMA.S_mse_4815847.entries n).filter (fun p => d < u*(p.1:ℤ)+v*p.2) =
      (OMA.S_mse_4815847.entries n).filter (fun p => (-u)*(p.1:ℤ)+(-v)*p.2 ≤ -d-1) := by
    apply Finset.filter_congr
    intro p _
    simp only [neg_mul]
    omega
  rw [hf]
  change mass n (-u) (-v) (-d-1) ≠ mass n u v d
  have hc := complement n u v d
  omega

end PascalCut

namespace PascalCut

/-- Read the explicitly stored pivots before a final-row vertex.
Return the pivots, the most recent column on row n-1, and the unread bytes. -/
def readPoints (n : ℕ) : ℕ → ℕ → ℕ → List Point × ℕ × ℕ
  | 0, col, z => ([], col, z)
  | count+1, col, z =>
    let row := z % 256
    let k := (z >>> 8) % 256
    let (ps,c,rest) := readPoints n count (if row = n-1 then k else col) (z >>> 16)
    ((row,k) :: ps, c, rest)

/-- Visit the final row in descending column order. Byte tags 0..127
encode runs in which the penultimate column increases by one. Tag 128
increments it by two. Larger tags give the number of explicit pivots plus 129. -/
def pivots (n : ℕ) : ℕ → ℕ → ℕ → List Point
  | 0, _, _ => []
  | j+1, col, z =>
    let tag := z % 256
    if tag ≤ 128 then
      let k := col + (if tag = 128 then 2 else 1)
      let rest := if 0 < tag ∧ tag < 128 then z-1 else z >>> 8
      (n-1,k) :: (n,j+1) :: pivots n j k rest
    else
      let (ps,k,rest) := readPoints n (tag-129) col (z >>> 8)
      ps ++ (n,j+1) :: pivots n j k rest

/-- Little-endian pivot instructions for each triangle size. -/
def instructions (n : ℕ) : ℕ :=
  List.getD [
    0, 0, 0x81,
    0x0, 0x81, 0x1,
    0x8003048281, 0x8004058200, 0x800004058281,
    0x8000040805068300, 0x800105068281, 0x8001050a06078300,
    0x800206078281, 0x8002060c07088300, 0x800307088281,
    0x8003070e08098300, 0x800408098281, 0x80040810090a8300,
    0x8005090a8281, 0x800509120a0b8300, 0x80060a0b8281,
    0x80060a140b0c8300, 0x80070b0c8281, 0x80070b160c0d8300,
    0x80080c0d8281, 0x80080c180d0e8300, 0x80090d0e8281,
    0x80090d1a0e0f8300, 0x800a0e0f8281, 0x800880111b820e1c0f108300,
    0x800b0f108281, 0x800980121d820f1e10118300, 0x800980141e820010118281,
    0x800a80131f82102011128300, 0x800a80152082141f11218311128281, 0x800a142282172182142182112212138300,
    0x800b80152282152112238312138281, 0x800b152482172382152382122413148300, 0x800c801624821424182113258413148281,
    0x800c162682182582182482132614158300, 0x800c1727821a268217268215268214158281, 0x800d8000182682142815168300,
    0x800d808018288216288215168281, 0x800d192a821d298200192882152a16178300, 0x800e8080192a82172a8216178281,
    0x800e80011a2a82162c17188300, 0x800f8000172d1c2b83182c8217188281, 0x800f8001192d82172e18198300,
    0x800f8002192e8218198281, 0x801080011a2f821830191a8300, 0x801080021a3082191a8281,
    0x801180011b318219321a1b8300, 0x801180021b32821a1b8281, 0x801180021c33821a341b1c8300,
    0x801280021c34821b1c8281, 0x801280021d35821b361c1d8300, 0x801280031d36821c1d8281,
    0x801380021e37821c381d1e8300, 0x801380031e38821d1e8281, 0x801480021f39821d3a1e1f8300,
    0x801480031f3a821e1f8281, 0x80148003203b821e3c1f208300, 0x80158003203c821f208281,
    0x80158003213d821f3e20218300, 0x80168003213e8220218281, 0x80168003223f82204021228300,
    0x8016800422408221228281, 0x80178003234182214222238300, 0x8017800423428222238281,
    0x80178004244382224423248300, 0x8018800424448223248281, 0x80188004254582234624258300,
    0x8019800425468224258281, 0x80198004264782244825268300, 0x8019800526488225268281,
    0x801a8004274982254a26278300, 0x801a8005274a8226278281, 0x801b8004284b82264c27288300,
    0x801b8005284c8227288281, 0x801b8005294d82274e28298300, 0x801c8005294e8228298281,
    0x801c80052a4f822850292a8300, 0x801c80062a5082292a8281, 0x801d80052b518229522a2b8300,
    0x801d80062b52822a2b8281, 0x801e80052c53822a542b2c8300, 0x801e80062c54822b2c8281,
    0x801e80062d55822b562c2d8300, 0x801f80062d56822c2d8281, 0x801f800380335782002e57822c582d2e8300,
    0x8020800380325882002e58822d2e8281, 0x8020800380345982002f59822d5a2e2f8300, 0x8020800480335a82002f5a822e2f8281,
    0x8021800380355b8200305b822e5c2f308300, 0x80218003325d82375c82345c8200305c822f308281, 0x8021800480365d8200315d822f5e30318300,
    0x80228003335f82385e82355e8200355b315e8330318281, 0x8022800480375f82385e3160833060395b325f84306031328300, 0x802380033461823e5f8236608200365d32608331328281,
    0x802380033562823b61823c608239603262833162385e336184316232338300, 0x8023800435638239628237628200375f33628332338281, 0x802480033664823b63823863823663823264376183326433348300,
    0x802480043665823a648238648200396034648333348281, 0x802580033766823c65823965823765823366386383336634358300, 0x802580033867823f66823b66823966820036658234358281,
    0x802580043868823d67823a67823867823468396583346835368300, 0x802680033969823f68823c68823e67820037678235368281, 0x8026800480803b6982396982356a3a6783356a36378300,
    0x802680043a6b82406a82376b4269833f69820038698236378281, 0x8027800480803c6b823a6b82366c3b6983366c37388300, 0x8027800480013f6b8200396b8237388281,
    0x802880033c6e82446d82803d6d823b6d82376e3c6b83376e38398300, 0x802880048001406d82003a6d8238398281, 0x802880043d7082446f82803e6f823c6f823870406b833870393a8300,
    0x8029800480013d7082003b6f82393a8281, 0x802980048000803f71823d718239723f6e8339723a3b8300, 0x8029800580013e7282003c71823a3b8281,
    0x802a80048000804073823e73823a744070833a743b3c8300, 0x802a8004407582497482013f7482003d73823b3c8281, 0x802b800480013c764574833f75823b764172833b763c3d8300,
    0x802b80048002407682003e75823c3d8281, 0x802b800580024077823c783f76833c783d3e8300, 0x802c80048002417882003f77823d3e8281,
    0x802c800580024179823d7a4078833d7a3e3f8300, 0x802d80048002427a82004079823e3f8281, 0x802d8004447c824e7b8202427b823e7c417a833e7c3f408300,
    0x802d80058002437c8200417b823f408281, 0x802e80048003437d823f7e427c833f7e40418300, 0x802e80058002447e8200427d8240418281,
    0x802e80058003447f824080437e83408041428300, 0x802f8005800245808200437f8241428281, 0x802f800580034581824182448083418242438300,
    0x80308004488382538282024682820044818242438281, 0x8030800580034683824284458283428443448300, 0x8030800580034784820045838243448281,
    0x8031800580034785824386468483438644458300, 0x8031800580034886820046858244458281, 0x8032800580034887824488478683448845468300,
    0x803280058003498882508545898347878245468281, 0x8032800680034c8882458a488883458a46478300, 0x8033800580034a8a824e88468b8348898246478281,
    0x8033800580044d8a82468c498a83468c47488300, 0x8033800680034b8c824f8a478d83498b8247488281, 0x8034800580044e8c82478e4a8c83478e48498300,
    0x8034800680034c8e824d8d488f834a8d8248498281, 0x8035800580044f8e8248904b8e834890494a8300, 0x8035800680034d90824e8f4991834b8f82494a8281,
    0x80358006800450908249924c908349924a4b8300, 0x8036800580044e92824f914a93834c91824a4b8281, 0x8036800680045192824a944d92834a944b4c8300,
    0x8037800580044f948250934b95834d93824b4c8281, 0x8037800680045294824b964e94834b964c4d8300, 0x8037800680044c9757948351954c97834e95824c4d8281,
    0x8038800680045695824c984f96834c984d4e8300, 0x8038800680044d995b958352974d99834f97824d4e8281, 0x8038800680055797824d9a5098834d9a4e4f8300,
    0x8039800680044e9b55998353994e9b835099824e4f8281, 0x8039800680055a98824e9c519a834e9c4f508300, 0x803a800680044f9d569b83549b4f9d83519b824f508281,
    0x803a80068005589b824f9e529c834f9e50518300, 0x803a80078004509f579d83559d509f83529d8250518281, 0x803b80068005599d8250a0539e8350a051528300,
    0x803b8006800551a1589f83569f51a183539f8251528281, 0x803b8007800557a08251a254a08351a252538300, 0x803c8006800552a359a18357a152a38354a18252538281,
    0x803c8007800558a28252a455a28352a453548300, 0x803d8006800553a55aa38358a353a58355a38253548281, 0x803d8007800559a48253a656a48353a654558300,
    0x803d8007800554a75ba58359a554a78356a58254558281, 0x803e800680065aa68254a857a68354a855568300, 0x803e8007800555a95fa6835aa755a98357a78255568281,
    0x803f800680065ba88255aa58a88355aa56578300, 0x803f8007800556ab60a88360a756ab8358a98256578281, 0x803f800780065caa8256ac59aa8356ac57588300,
    0x80408007800557ad64a98363a857ad8359ab8257588281, 0x8040800780065dac8257ae5aac8357ae58598300, 0x80408008800558af825fac58af835aad8258598281,
    0x8041800780065eae8258b05bae8358b0595a8300, 0x80418007800659b18260ae59b1835baf82595a8281, 0x8042800780065fb08259b25cb08359b25a5b8300,
    0x8042800780038063b282005ab38261b05ab3835cb1825a5b8281, 0x80428008800660b2825ab45db2835ab45b5c8300, 0x8043800780038064b482005bb58262b25bb5835db3825b5c8281,
    0x8043800880028066b58270b35db6830061b4825bb65eb4835bb65c5d8300, 0x8044800780038065b682005cb78263b45cb7835eb5825c5d8281, 0x80448007800360b88267b78264b7820062b6825cb85fb6835cb85d5e8300,
    0x8044800880038066b882005db98264b65db9835fb7825d5e8281, 0x80458007800361ba8268b98265b9820063b8825dba60b8835dba5e5f8300, 0x80458008800262bb826aba8267ba82005ebb8260ba67b75ebb8460b9825e5f8281,
    0x80458008800362bc8269bb8266bb820064ba825ebc61ba835ebc5f608300, 0x80468008800263bd826bbc8268bc82005fbd8261bc68b95fbd8461bb825f608281, 0x80468008800363be826abd8267bd820065bc825fbe62bc835fbe60618300,
    0x80478007800364bf826cbe8269be820060bf8262be6bba60bf8462bd8260618281, 0x80478008800364c08272be8268bf820066be8260c063be8360c061628300, 0x80478008800365c1826dc0826ac0826dbf62c1830063c08263bf8261628281,
    0x80488008800266c2826fc1826bc18269c1820064c16cbe8361c264c08361c262638300, 0x80488008800366c3826dc28272c1826ec163c3830064c28264c18262638281, 0x80498008800267c48270c3826cc3826ac3820065c38262c465c28362c463648300,
    0x80498008800367c5826ec4826bc48274c264c5830065c48265c38263648281, 0x80498008800368c6827ac4826dc5826bc5820066c58263c666c48363c664658300, 0x804a8008800368c7826fc6826cc6826ac6820066c68266c58264658281,
    0x804a8008800369c88271c7826ec7826cc7820067c78264c867c68364c865668300, 0x804a800980026ac98274c88270c8826dc8826bc8820067c88267c78265668281, 0x804b800880036aca8272c9826fc9826dc9820068c98265ca68c88365ca66678300,
    0x804b800980026bcb8275ca8271ca826eca826cca820068ca8268c98266678281, 0x804c800880036bcc8273cb8270cb826ecb820069cb8266cc69ca8366cc67688300, 0x804c800880036ccd8275cc82806fcc826dcc820069cc8269cb8267688281,
    0x804c80098003808071cd8275cc82006acd8267ce6acc8367ce68698300, 0x804d800880036dcf8276ce828070ce826ece82006ace826acd8268698281, 0x804d80098003808072cf8276ce82006bcf8268d06bce8368d0696a8300,
    0x804d800980036ed18277d0828071d0826fd082006bd0826bcf82696a8281, 0x804e800980026fd2827ad1820176d082006cd18269d26cd08369d26a6b8300, 0x804e8009800380008072d28270d282006cd2826cd1826a6b8281,
    0x804f8008800370d4827bd3820177d282006dd3826ad46dd2836ad46b6c8300, 0x804f8009800380008073d48271d482006dd4826dd3826b6c8281, 0x804f8009800371d6827bd5820172d582006ed5826bd66ed4836bd66c6d8300,
    0x80508009800380008074d68272d682006ed6826ed5826c6d8281, 0x80508009800372d8827cd7820173d782006fd7826cd86fd6836cd86d6e8300, 0x80518009800380008075d88273d882006fd88274d36fd7836d6e8281,
    0x805180098003800274d9820070d9826dda70d8836dda6e6f8300, 0x8051800a800274db8280da82008076da8274da820070da8275d570d9836e6f8281, 0x805280098003800275db820071db826edc71da836edc6f708300,
    0x80528009800375dd8280dc82008077dc8275dc820071dc8276d771db836f708281, 0x8052800a8003800276dd820072dd826fde72dc836fde70718300, 0x80538009800376df8281de820171df7edd8376de820072de8278d872dd8370718281,
    0x8053800a8003800277df820073df8270e073de8370e071728300, 0x805480098003800272e17fdf8377e0820073e08274de8271728281, 0x8054800a8003800278e1820074e18271e274e08371e272738300,
    0x8054800a8003800378e2820074e28275e08272738281, 0x805580098004800279e3820075e38272e475e28372e473748300, 0x8055800a8003800379e4820075e48276e28273748281,
    0x8056800980037ae68286e582027ae58282e374e68376e58273e676e48373e674758300, 0x8056800a800380037ae6820076e68277e48274758281, 0x8056800a800380037be7827ee675e88377e78274e877e68374e875768300,
    0x8057800a800380037be8820077e88278e68275768281, 0x8057800a800380037ce9827fe876ea8378e98275ea78e88375ea76778300, 0x8057800a800480037cea820078ea8279e88276778281,
    0x8058800a800380037deb8280ea77ec8379eb8276ec7de78376ec77788300, 0x8058800a800480037dec820079ec827aea8277788281, 0x8059800a800380037eed8281ec78ee837aed8277ee7ee98377ee78798300,
    0x8059800a80037fef828dee820383ed82007aee827bec8278798281, 0x8059800b800380037fef8282ee79f0837bef8278f07feb8378f0797a8300, 0x805a800a8003800484ef82007bf0827cee82797a8281,
    0x805a800a8004800380f18283f07af2837cf18279f280ed8379f27a7b8300, 0x805a800b8003800485f182007cf2827df0827a7b8281, 0x805b800a8004800381f38284f27bf4837df3827af481ef837af47b7c8300,
    0x805b800b8003800486f382007df4827ef2827b7c8281, 0x805c800a8004800382f58289f37cf6837ef5827bf682f1837bf67c7d8300, 0x805c800b8003800487f582007ef6827ff4827c7d8281,
    0x805c800b8004800383f7828af57df8837ff7827cf883f3837cf87d7e8300, 0x805d800a800480048df682007ff88280f6827d7e8281] n 0

def sizeCheck (n : ℕ) : Bool :=
  checkRow n && (decide (n < 2) ||
    coverPoints n (pivots n (n/2) (n/2-1) (instructions n)) ⟨-1,2⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem sizes (n : ℕ) (hn : n ≤ 250) : sizeCheck n = true := by
  interval_cases n <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem weights_correct (r k : ℕ) (hr : r ≤ 250) (hk : k ≤ r) : val r k = rowPrefix r k :=
  valid_of_checks (by decide +kernel) (fun n hn => (Bool.and_eq_true_iff.mp (sizes n (by omega))).1)
    r k hr (by omega)

end PascalCut

theorem OMA.solution : OMA.R_mse_4815847_R1.H1 := by
  intro n h₂ hn u v d _ _ _
  have hc := (Bool.and_eq_true_iff.mp (PascalCut.sizes n hn)).2
  simp only [show ¬ n < 2 by omega, decide_false, Bool.false_or] at hc
  exact PascalCut.solved_size PascalCut.weights_correct n hn _ hc u v d
