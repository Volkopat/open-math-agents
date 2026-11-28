import OMAReductions.R_Erdos835_erdos_835_R1
import Mathlib

open Finset
namespace F2E835

def ofMask (m : ℕ) : Finset (Fin 32) :=
  (Finset.univ : Finset (Fin 32)).filter (fun i => m.testBit i.val = true)

/-- Number of set bits among the lowest `n` bits. -/
def popc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => m % 2 + popc n (m / 2)

theorem card_bits (n m : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => m.testBit i.val = true)).card = popc n m := by
  induction n generalizing m with
  | zero => simp [popc]
  | succ n ih =>
    rw [Finset.card_filter, Fin.sum_univ_succ, popc, ← ih (m / 2), Finset.card_filter]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ, Nat.testBit_succ]

theorem inter_card (a b : ℕ) : (ofMask a ∩ ofMask b).card = popc 32 (a &&& b) := by
  unfold ofMask
  rw [← Finset.filter_and, ← card_bits]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp [Nat.testBit_and]

def Mrows : List (List Nat) := [[33, 49, 65, 81, 97, 113, 129, 145], [19, 56, 77, 114, 133, 152, 183, 202], [26, 40, 61, 75, 96, 149, 218, 271], [20, 39, 80, 115, 127, 168, 184, 203], [23, 42, 58, 79, 98, 163, 219, 254], [21, 47, 59, 100, 116, 128, 181, 220], [22, 46, 62, 83, 109, 146, 167, 237], [27, 50, 66, 82, 91, 132, 148, 164], [32, 48, 64, 78, 94, 110, 135, 199], [25, 41, 55, 101, 117, 166, 182, 201], [29, 45, 57, 76, 92, 169, 185, 235], [24, 37, 84, 99, 112, 151, 165, 200], [30, 43, 63, 74, 93, 130, 186, 253], [28, 38, 67, 95, 111, 134, 150, 217], [31, 44, 60, 73, 118, 131, 147, 236]]

def Xset : Finset (Fin 32) := (Finset.univ : Finset (Fin 32)).filter (fun x => 17 ≤ x.val)

def Llist : List (Finset (Fin 32)) :=
  (insert 0 Xset) :: (Mrows.zipIdx.flatMap (fun (r,j) =>
    r.map fun t => insert (Fin.ofNat 32 (t/17))
      (insert (Fin.ofNat 32 (t%17)) (Xset.erase (Fin.ofNat 32 (17+j))))))

def Dlist : List (Finset (Fin 32)) := Llist ++ Llist.map (fun B => Finset.univ \ B)

def masks := Dlist.map fun B => ∑ i ∈ B, 2 ^ i.val

theorem hD : Dlist = masks.map ofMask := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem hp : ∀ a ∈ masks, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by decide +kernel

end F2E835

open F2E835 in
theorem OMA.solution : OMA.R_Erdos835_erdos_835_R1.H1 := by
  show ∀ A ∈ Dlist, ∀ B ∈ Dlist, A ≠ B → (A ∩ B).card ≠ 15
  rw [hD]
  intro A hA B hB _
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  rw [inter_card]
  exact hp a ha b hb
