import OMAStatements.S_mo_370694
import Mathlib.Tactic

-- Reduction of the root-gathering problem to a bounded core and a six-level strip.
-- Credit: @Chihiro-g
namespace OMA.R_mo_370694_R1

open OMA.S_mo_370694



/-- Exponential supply of available bottom cherries in the large-height regime. -/
theorem powerDominates (s : ℕ) (hs : 32 ≤ s) : (64*s)^2 ≤ 2^(s-2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hs
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 32+(n+1)-2 = (32+n-2)+1 := by omega
    rw [he, pow_succ]
    calc
      (64*(32+(n+1)))^2 ≤ 2*(64*(32+n))^2 := by nlinarith [Nat.zero_le (n^2)]
      _ ≤ _ := by omega

/-- Split U cherries into chains with q and q-1 cherries. -/
theorem chainCounts {q U : ℕ} (hq : 2 ≤ q) (hb : q*q ≤ U) :
    ∃ x y : ℕ, q*x + (q-1)*y = U ∧ (q-1)*(x+y) ≤ U := by
  have hd := Nat.div_add_mod U q
  have he : q - 1 + 1 = q := by omega
  have hbound : q ≤ U/q := (Nat.le_div_iff_mul_le (by omega)).mpr hb
  by_cases hh : U%q = 0
  · refine ⟨U/q,0,?_,?_⟩
    · simpa [hh] using hd
    · simp only [Nat.add_zero, hh] at *
      nlinarith [Nat.mul_le_mul_right (U/q) (Nat.sub_le q 1)]
  · have hm := Nat.mod_lt U (by omega : 0 < q)
    let y := q-U%q
    have hy : y + U%q = q := by dsimp [y]; omega
    let x := U/q+1-y
    have hx : x+y = U/q+1 := by dsimp [x]; omega
    have mul := congrArg (fun m : ℕ => q*m) hx
    have submul := congrArg (fun m : ℕ => m*y) he
    have eq : q*x+(q-1)*y = U := by nlinarith
    refine ⟨x,y,eq,?_⟩
    nlinarith [Nat.mul_le_mul_right x (Nat.sub_le q 1)]

/-- Per-copy capacities for the six-level strip. One cherry has three frogs.
The two terminal depths are 3q and 3q-3, and a seed contains s cherries. -/
theorem parameters (h : ℕ) (hh : 129 ≤ h) :
    ∃ e x y : ℕ, let s := 2^e; let L := s+3; let A := 2^(L-5); let q := h/3
      16 ≤ s ∧ L < h ∧ 2*L+2 ≤ 3*s ∧ s < q-1 ∧
      q*x+(q-1)*y = 21*A ∧ x+y ≤ A ∧ s*(x+y) ≤ 8*A := by
  have finish (s : ℕ) (hcap : 21*s ≤ 8*(h/3-1))
      (hbig : h/3*(h/3) ≤ 21*2^(s-2)) :
      ∃ x y : ℕ, h/3*x+(h/3-1)*y=21*2^(s-2) ∧ x+y ≤ 2^(s-2) ∧
        s*(x+y) ≤ 8*2^(s-2) := by
    obtain ⟨x,y,hxy,hm⟩ := chainCounts (q := h/3) (by omega) hbig
    have a := Nat.mul_le_mul_right (x+y) (by omega : 21 ≤ h/3-1)
    have b := Nat.mul_le_mul_right (x+y) hcap
    refine ⟨x,y,hxy,by nlinarith,?_⟩
    nlinarith [Nat.mul_le_mul_left 8 hm]
  by_cases small : h < 1024
  · have hq : h/3 ≤ 341 := by omega
    have hc : 21*16 ≤ 8*(h/3-1) := by omega
    have hb : h/3*(h/3) ≤ 21*2^(16-2) :=
      (Nat.mul_le_mul hq hq).trans (by decide)
    obtain ⟨x,y,hxy,h1,h2⟩ := finish 16 hc hb
    exact ⟨4,x,y,by decide,by omega,by decide,by omega,hxy,h1,h2⟩
  · let e := Nat.log 2 (h/32)
    let s := 2^e
    have lo : s ≤ h/32 := Nat.pow_log_le_self 2 (by omega)
    have hi : h/32 < 2*s := by
      simpa [s,e,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (b:=2) (by decide) (h/32)
    have hs : 32 ≤ s := by
      have he : 5 ≤ e := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
      exact Nat.pow_le_pow_right (by decide : 0 < 2) he
    have sq := powerDominates s hs
    have hq : h/3 ≤ 64*s := by omega
    have hc : 21*s ≤ 8*(h/3-1) := by omega
    have hb : h/3*(h/3) ≤ 21*2^(s-2) := by
      have a := Nat.mul_le_mul hq hq
      nlinarith
    obtain ⟨x,y,hxy,h1,h2⟩ := finish s hc hb
    refine ⟨e,x,y,?_⟩
    change 16 ≤ s ∧ s+3 < h ∧ 2*(s+3)+2 ≤ 3*s ∧ s < h/3-1 ∧
      h/3*x+(h/3-1)*y = 21*2^(s+3-5) ∧ x+y ≤ 2^(s+3-5) ∧ s*(x+y) ≤ 8*2^(s+3-5)
    rw [show s+3-5=s-2 by omega]
    exact ⟨by omega, by omega, by omega, by omega, hxy, h1, h2⟩


/-- Finish a core of height at most 128. Frogs from higher levels are already at
the root. Distances and moves are those of the original ambient tree. -/
def H1 : Prop :=
  ∀ h k : ℕ, k ≤ h → k ≤ 128 → k ≠ 2 →
    Relation.ReflTransGen (Move h)
      (fun v => if v.val = 0 then 2^(h+1) - 2^(k+1) + 1
                else if v.val + 1 < 2^(k+1) then 1 else 0)
      (fun v => if v.val = 0 then 2^(h+1) - 1 else 0)

/-- Transfer the six deepest occupied non-root layers to the root, leaving every
frog in the smaller core in place. This is one strip, at arbitrary depth. -/
def H2 : Prop :=
  ∀ h k : ℕ, k ≤ h → 129 ≤ k →
    Relation.ReflTransGen (Move h)
      (fun v => if v.val = 0 then 2^(h+1) - 2^(k+1) + 1
                else if v.val + 1 < 2^(k+1) then 1 else 0)
      (fun v => if v.val = 0 then 2^(h+1) - 2^(k-6+1) + 1
                else if v.val + 1 < 2^(k-6+1) then 1 else 0)

theorem main : H1 → H2 → type_of% @OMA.S_mo_370694.main := by
  intro small strip h hne
  let core (k : ℕ) : Vertex h → ℕ := fun v =>
    if v.val = 0 then 2^(h+1) - 2^(k+1) + 1
    else if v.val + 1 < 2^(k+1) then 1 else 0
  have finish (k : ℕ) (hk : k ≤ h) (hne' : k ≠ 2) :
      Relation.ReflTransGen (Move h) (core k)
        (fun v => if v.val = 0 then 2^(h+1) - 1 else 0) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hb : k ≤ 128
      · exact small h k hk hb hne'
      · exact (strip h k hk (by omega)).trans (ih (k-6) (by omega) (by omega) (by omega))
  have initial : core h = fun _ => 1 := by
    funext v
    have hv := v.isLt
    change v.val < 2^(h+1)-1 at hv
    have hb : v.val+1 < 2^(h+1) := by omega
    simp [core, hb]
  simpa only [initial] using finish h (le_refl _) hne

end OMA.R_mo_370694_R1
