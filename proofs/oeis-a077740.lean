import OMAStatements.S_oeis_a077740
import Mathlib

open scoped Pointwise

namespace OMA.A077740Port


/-- les elements {2,5}-smooth de X : 16 signes. -/
def Xsmooth25 : List ℤ :=
  [1, 2, 4, 8, 10, 20, 32, 40, -1, -2, -4, -8, -10, -20, -32, -40]

/-- les elements {2,3,5}-smooth de X : 28 signes. -/
def Xsmooth235 : List ℤ :=
  [1, 2, 3, 4, 8, 9, 10, 12, 18, 20, 24, 30, 32, 40,
   -1, -2, -3, -4, -8, -9, -10, -12, -18, -20, -24, -30, -32, -40]

/-- residu canonique de `x : Int` dans `[0, M)` en `Nat`. -/
def xres (M : Nat) (x : Int) : Nat := (((x % (M : Int)) + M) % M).toNat

/-- etage `j` en residus `Nat` (coefficient `(9/g)*10^{3j} mod M`). -/
def stageRes (M j g : Nat) (xs : List Int) : List Nat :=
  let c := ((9 / g) * 10 ^ (3 * j)) % M
  (xs.map (fun x => (c * xres M x) % M)).eraseDups

/-- positions `< M` a bit `1`. -/
def setBits (M : Nat) (bits : Nat) : List Nat :=
  (List.range M).filter fun r => bits.testBit r

/-- `acc ∪ (acc + stage mod M)` en bits. -/
def step (M : Nat) (acc : Nat) (stage : List Nat) : Nat :=
  (setBits M acc).foldl
    (fun a r => stage.foldl (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a)
    acc

/-- `jmax` etages depuis le bit `0`. -/
def coverBits (M g : Nat) (xs : List Int) (jmax : Nat) : Nat :=
  (List.range jmax).foldl (fun acc j => step M acc (stageRes M (j+1) g xs)) 1

/-- certificat bitmap : tous les bits `< M` poses. -/
def checkCoverB (M g : Nat) (xs : List Int) (jmax : Nat) : Bool :=
  coverBits M g xs jmax == (1 <<< M) - 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
theorem auxp_cA : ((List.range' 1 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
theorem auxp_cB : ((List.range' 415 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
theorem auxp_cC : ((List.range' 829 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
theorem auxp_cD : ((List.range' 1243 414).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
/-- Certificat machine : pour tout m <= 1656 premier a 10 hors
    {11,19,23} avec M = m / gcd(9,m) <= 184, il existe
    k <= m/27+1 etages couvrant ZMod M. -/
theorem stage_cover_small_aux' :
    ((List.range' 1 1656).all fun m =>
      (!(Nat.gcd m 10 == 1)) ||
      (decide (m = 11)) || (decide (m = 19)) || (decide (m = 23)) ||
      (!(decide (m / Nat.gcd 9 m ≤ 184))) ||
      ((List.range (m / 27 + 2)).any fun k =>
        checkCoverB (m / Nat.gcd 9 m) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k))
    = true := by
  have hsplit : List.range' 1 1656 =
      List.range' 1 414 ++ List.range' 415 414 ++ List.range' 829 414 ++ List.range' 1243 414 := by
    decide
  rw [hsplit, List.all_append, List.all_append,
      List.all_append, auxp_cA, auxp_cB, auxp_cC, auxp_cD]
  decide

def witCorner : List (ℕ × ℕ × ℕ × ℕ) := [
    (11, 7, 0, 8881300),
    (11, 7, 1, 8866000),
    (11, 7, 2, 8880400),
    (11, 7, 3, 8875000),
    (11, 7, 4, 8780500),
    (11, 7, 5, 8884000),
    (11, 7, 6, 8680600),
    (11, 7, 7, 8883100),
    (11, 7, 8, 8848000),
    (11, 7, 9, 8882200),
    (11, 7, 10, 8857000),
    (11, 7, 0, 8867000),
    (11, 7, 1, 8881400),
    (11, 7, 2, 8876000),
    (11, 7, 3, 8880500),
    (11, 7, 4, 8885000),
    (11, 7, 5, 8780600),
    (11, 7, 6, 8884100),
    (11, 7, 7, 8680700),
    (11, 7, 8, 8883200),
    (11, 7, 9, 8858000),
    (11, 7, 10, 8882300),
    (11, 7, 0, 8882400),
    (11, 7, 1, 8877000),
    (11, 7, 2, 8881500),
    (11, 7, 3, 8886000),
    (11, 7, 4, 8880600),
    (11, 7, 5, 8885100),
    (11, 7, 6, 8780700),
    (11, 7, 7, 8884200),
    (11, 7, 8, 8680800),
    (11, 7, 9, 8883300),
    (11, 7, 10, 8868000),
    (11, 7, 0, 8878000),
    (11, 7, 1, 8882500),
    (11, 7, 2, 8887000),
    (11, 7, 3, 8881600),
    (11, 7, 4, 8886100),
    (11, 7, 5, 8880700),
    (11, 7, 6, 8885200),
    (11, 7, 7, 8780800),
    (11, 7, 8, 8884300),
    (11, 7, 9, 8868010),
    (11, 7, 10, 8883400),
    (11, 7, 0, 8883500),
    (11, 7, 1, 8888000),
    (11, 7, 2, 8882600),
    (11, 7, 3, 8887100),
    (11, 7, 4, 8881700),
    (11, 7, 5, 8886200),
    (11, 7, 6, 8880800),
    (11, 7, 7, 8885300),
    (11, 7, 8, 8868020),
    (11, 7, 9, 8884400),
    (11, 7, 10, 8878010),
    (11, 8, 0, 88880000),
    (11, 8, 1, 88835000),
    (11, 8, 2, 88780100),
    (11, 8, 3, 88844000),
    (11, 8, 4, 88680200),
    (11, 8, 5, 88853000),
    (11, 8, 6, 88808000),
    (11, 8, 7, 88862000),
    (11, 8, 8, 88817000),
    (11, 8, 9, 88871000),
    (11, 8, 10, 88826000),
    (11, 8, 0, 88836000),
    (11, 8, 1, 88880100),
    (11, 8, 2, 88845000),
    (11, 8, 3, 88780200),
    (11, 8, 4, 88854000),
    (11, 8, 5, 88680300),
    (11, 8, 6, 88863000),
    (11, 8, 7, 88818000),
    (11, 8, 8, 88872000),
    (11, 8, 9, 88827000),
    (11, 8, 10, 88881000),
    (11, 8, 0, 88881100),
    (11, 8, 1, 88846000),
    (11, 8, 2, 88880200),
    (11, 8, 3, 88855000),
    (11, 8, 4, 88780300),
    (11, 8, 5, 88864000),
    (11, 8, 6, 88680400),
    (11, 8, 7, 88873000),
    (11, 8, 8, 88828000),
    (11, 8, 9, 88882000),
    (11, 8, 10, 88837000),
    (11, 8, 0, 88847000),
    (11, 8, 1, 88881200),
    (11, 8, 2, 88856000),
    (11, 8, 3, 88880300),
    (11, 8, 4, 88865000),
    (11, 8, 5, 88780400),
    (11, 8, 6, 88874000),
    (11, 8, 7, 88680500),
    (11, 8, 8, 88883000),
    (11, 8, 9, 88838000),
    (11, 8, 10, 88882100),
    (11, 8, 0, 88882200),
    (11, 8, 1, 88857000),
    (11, 8, 2, 88881300),
    (11, 8, 3, 88866000),
    (11, 8, 4, 88880400),
    (11, 8, 5, 88875000),
    (11, 8, 6, 88780500),
    (11, 8, 7, 88884000),
    (11, 8, 8, 88680600),
    (11, 8, 9, 88883100),
    (11, 8, 10, 88848000),
    (11, 9, 0, 888570000),
    (11, 9, 1, 888822000),
    (11, 9, 2, 888480000),
    (11, 9, 3, 888831000),
    (11, 9, 4, 886806000),
    (11, 9, 5, 888840000),
    (11, 9, 6, 887805000),
    (11, 9, 7, 888750000),
    (11, 9, 8, 888804000),
    (11, 9, 9, 888660000),
    (11, 9, 10, 888813000),
    (11, 9, 0, 888823000),
    (11, 9, 1, 888580000),
    (11, 9, 2, 888832000),
    (11, 9, 3, 886807000),
    (11, 9, 4, 888841000),
    (11, 9, 5, 887806000),
    (11, 9, 6, 888850000),
    (11, 9, 7, 888805000),
    (11, 9, 8, 888760000),
    (11, 9, 9, 888814000),
    (11, 9, 10, 888670000),
    (11, 9, 0, 888680000),
    (11, 9, 1, 888833000),
    (11, 9, 2, 886808000),
    (11, 9, 3, 888842000),
    (11, 9, 4, 887807000),
    (11, 9, 5, 888851000),
    (11, 9, 6, 888806000),
    (11, 9, 7, 888860000),
    (11, 9, 8, 888815000),
    (11, 9, 9, 888770000),
    (11, 9, 10, 888824000),
    (11, 9, 0, 888834000),
    (11, 9, 1, 888680100),
    (11, 9, 2, 888843000),
    (11, 9, 3, 887808000),
    (11, 9, 4, 888852000),
    (11, 9, 5, 888807000),
    (11, 9, 6, 888861000),
    (11, 9, 7, 888816000),
    (11, 9, 8, 888870000),
    (11, 9, 9, 888825000),
    (11, 9, 10, 888780000),
    (11, 9, 0, 888780100),
    (11, 9, 1, 888844000),
    (11, 9, 2, 888680200),
    (11, 9, 3, 888853000),
    (11, 9, 4, 888808000),
    (11, 9, 5, 888862000),
    (11, 9, 6, 888817000),
    (11, 9, 7, 888871000),
    (11, 9, 8, 888826000),
    (11, 9, 9, 888880000),
    (11, 9, 10, 888835000),
    (19, 7, 0, 7786000),
    (19, 7, 1, 6787000),
    (19, 7, 2, 8866000),
    (19, 7, 3, 7867000),
    (19, 7, 4, 6868000),
    (19, 7, 5, 8776000),
    (19, 7, 6, 7777000),
    (19, 7, 7, 6778000),
    (19, 7, 8, 8686000),
    (19, 7, 9, 8884000),
    (19, 7, 10, 7885000),
    (19, 7, 11, 6886000),
    (19, 7, 12, 5887000),
    (19, 7, 13, 4888000),
    (19, 7, 14, 8677000),
    (19, 7, 15, 8875000),
    (19, 7, 16, 7876000),
    (19, 7, 17, 6877000),
    (19, 7, 18, 8785000),
    (19, 7, 0, 8677100),
    (19, 7, 1, 8687000),
    (19, 7, 2, 8885000),
    (19, 7, 3, 7886000),
    (19, 7, 4, 6887000),
    (19, 7, 5, 5888000),
    (19, 7, 6, 6787100),
    (19, 7, 7, 8678000),
    (19, 7, 8, 8876000),
    (19, 7, 9, 7877000),
    (19, 7, 10, 6878000),
    (19, 7, 11, 8786000),
    (19, 7, 12, 7787000),
    (19, 7, 13, 6788000),
    (19, 7, 14, 8867000),
    (19, 7, 15, 7868000),
    (19, 7, 16, 6886100),
    (19, 7, 17, 8777000),
    (19, 7, 18, 7778000),
    (19, 7, 0, 8867100),
    (19, 7, 1, 8877000),
    (19, 7, 2, 7878000),
    (19, 7, 3, 8777100),
    (19, 7, 4, 8787000),
    (19, 7, 5, 7788000),
    (19, 7, 6, 8687100),
    (19, 7, 7, 8868000),
    (19, 7, 8, 7886100),
    (19, 7, 9, 6887100),
    (19, 7, 10, 8778000),
    (19, 7, 11, 6787200),
    (19, 7, 12, 8678100),
    (19, 7, 13, 8688000),
    (19, 7, 14, 8886000),
    (19, 7, 15, 7887000),
    (19, 7, 16, 6888000),
    (19, 7, 17, 7787100),
    (19, 7, 18, 6788100),
    (19, 7, 0, 8886100),
    (19, 7, 1, 7887100),
    (19, 7, 2, 6888100),
    (19, 7, 3, 7787200),
    (19, 7, 4, 6788200),
    (19, 7, 5, 8867200),
    (19, 7, 6, 8877100),
    (19, 7, 7, 8887000),
    (19, 7, 8, 7888000),
    (19, 7, 9, 8787100),
    (19, 7, 10, 7788100),
    (19, 7, 11, 8687200),
    (19, 7, 12, 8868100),
    (19, 7, 13, 8878000),
    (19, 7, 14, 6887200),
    (19, 7, 15, 8778100),
    (19, 7, 16, 8788000),
    (19, 7, 17, 8678200),
    (19, 7, 18, 8688100),
    (19, 7, 0, 8888000),
    (19, 7, 1, 8778200),
    (19, 7, 2, 8788100),
    (19, 7, 3, 8678300),
    (19, 7, 4, 8688200),
    (19, 7, 5, 8886200),
    (19, 7, 6, 7887200),
    (19, 7, 7, 6888200),
    (19, 7, 8, 7787300),
    (19, 7, 9, 6788300),
    (19, 7, 10, 8867300),
    (19, 7, 11, 8877200),
    (19, 7, 12, 8887100),
    (19, 7, 13, 7888100),
    (19, 7, 14, 8787200),
    (19, 7, 15, 7788200),
    (19, 7, 16, 8687300),
    (19, 7, 17, 8868200),
    (19, 7, 18, 8878100),
    (19, 8, 0, 88682000),
    (19, 8, 1, 88880000),
    (19, 8, 2, 87881000),
    (19, 8, 3, 86882000),
    (19, 8, 4, 78872000),
    (19, 8, 5, 77873000),
    (19, 8, 6, 88673000),
    (19, 8, 7, 88871000),
    (19, 8, 8, 87872000),
    (19, 8, 9, 86873000),
    (19, 8, 10, 88781000),
    (19, 8, 11, 87782000),
    (19, 8, 12, 86783000),
    (19, 8, 13, 88862000),
    (19, 8, 14, 68882000),
    (19, 8, 15, 67883000),
    (19, 8, 16, 88772000),
    (19, 8, 17, 78881000),
    (19, 8, 18, 77882000),
    (19, 8, 0, 88872000),
    (19, 8, 1, 87873000),
    (19, 8, 2, 86874000),
    (19, 8, 3, 88782000),
    (19, 8, 4, 87783000),
    (19, 8, 5, 86784000),
    (19, 8, 6, 88863000),
    (19, 8, 7, 68883000),
    (19, 8, 8, 67884000),
    (19, 8, 9, 88773000),
    (19, 8, 10, 78882000),
    (19, 8, 11, 77883000),
    (19, 8, 12, 88683000),
    (19, 8, 13, 88881000),
    (19, 8, 14, 87882000),
    (19, 8, 15, 86883000),
    (19, 8, 16, 78873000),
    (19, 8, 17, 77874000),
    (19, 8, 18, 88674000),
    (19, 8, 0, 68884000),
    (19, 8, 1, 67885000),
    (19, 8, 2, 88774000),
    (19, 8, 3, 78883000),
    (19, 8, 4, 77884000),
    (19, 8, 5, 88684000),
    (19, 8, 6, 88882000),
    (19, 8, 7, 87883000),
    (19, 8, 8, 86884000),
    (19, 8, 9, 78874000),
    (19, 8, 10, 77875000),
    (19, 8, 11, 88675000),
    (19, 8, 12, 88873000),
    (19, 8, 13, 87874000),
    (19, 8, 14, 86875000),
    (19, 8, 15, 88783000),
    (19, 8, 16, 87784000),
    (19, 8, 17, 86785000),
    (19, 8, 18, 88864000),
    (19, 8, 0, 87884000),
    (19, 8, 1, 86885000),
    (19, 8, 2, 78875000),
    (19, 8, 3, 77876000),
    (19, 8, 4, 88676000),
    (19, 8, 5, 88874000),
    (19, 8, 6, 87875000),
    (19, 8, 7, 86876000),
    (19, 8, 8, 88784000),
    (19, 8, 9, 87785000),
    (19, 8, 10, 86786000),
    (19, 8, 11, 88865000),
    (19, 8, 12, 68885000),
    (19, 8, 13, 67886000),
    (19, 8, 14, 88775000),
    (19, 8, 15, 78884000),
    (19, 8, 16, 77885000),
    (19, 8, 17, 88685000),
    (19, 8, 18, 88883000),
    (19, 8, 0, 86877000),
    (19, 8, 1, 88785000),
    (19, 8, 2, 87786000),
    (19, 8, 3, 86787000),
    (19, 8, 4, 88866000),
    (19, 8, 5, 68886000),
    (19, 8, 6, 67887000),
    (19, 8, 7, 88776000),
    (19, 8, 8, 78885000),
    (19, 8, 9, 77886000),
    (19, 8, 10, 88686000),
    (19, 8, 11, 88884000),
    (19, 8, 12, 87885000),
    (19, 8, 13, 86886000),
    (19, 8, 14, 78876000),
    (19, 8, 15, 77877000),
    (19, 8, 16, 88677000),
    (19, 8, 17, 88875000),
    (19, 8, 18, 87876000),
    (19, 9, 0, 888750000),
    (19, 9, 1, 868770000),
    (19, 9, 2, 877860000),
    (19, 9, 3, 888660000),
    (19, 9, 4, 678870000),
    (19, 9, 5, 788850000),
    (19, 9, 6, 886860000),
    (19, 9, 7, 878850000),
    (19, 9, 8, 788760000),
    (19, 9, 9, 886770000),
    (19, 9, 10, 878760000),
    (19, 9, 11, 887850000),
    (19, 9, 12, 867870000),
    (19, 9, 13, 688860000),
    (19, 9, 14, 887760000),
    (19, 9, 15, 778860000),
    (19, 9, 16, 888840000),
    (19, 9, 17, 868860000),
    (19, 9, 18, 778770000),
    (19, 9, 0, 688870000),
    (19, 9, 1, 887770000),
    (19, 9, 2, 778870000),
    (19, 9, 3, 888850000),
    (19, 9, 4, 868870000),
    (19, 9, 5, 778780000),
    (19, 9, 6, 888760000),
    (19, 9, 7, 868780000),
    (19, 9, 8, 877870000),
    (19, 9, 9, 888670000),
    (19, 9, 10, 678880000),
    (19, 9, 11, 788860000),
    (19, 9, 12, 886870000),
    (19, 9, 13, 878860000),
    (19, 9, 14, 788770000),
    (19, 9, 15, 886780000),
    (19, 9, 16, 878770000),
    (19, 9, 17, 887860000),
    (19, 9, 18, 867880000),
    (19, 9, 0, 878870000),
    (19, 9, 1, 788780000),
    (19, 9, 2, 888671000),
    (19, 9, 3, 878780000),
    (19, 9, 4, 887870000),
    (19, 9, 5, 886871000),
    (19, 9, 6, 688880000),
    (19, 9, 7, 887780000),
    (19, 9, 8, 778880000),
    (19, 9, 9, 888860000),
    (19, 9, 10, 868880000),
    (19, 9, 11, 867881000),
    (19, 9, 12, 888770000),
    (19, 9, 13, 887771000),
    (19, 9, 14, 877880000),
    (19, 9, 15, 888680000),
    (19, 9, 16, 868871000),
    (19, 9, 17, 788870000),
    (19, 9, 18, 886880000),
    (19, 9, 0, 887781000),
    (19, 9, 1, 778881000),
    (19, 9, 2, 888861000),
    (19, 9, 3, 868881000),
    (19, 9, 4, 788880000),
    (19, 9, 5, 888771000),
    (19, 9, 6, 878880000),
    (19, 9, 7, 877881000),
    (19, 9, 8, 888681000),
    (19, 9, 9, 868872000),
    (19, 9, 10, 887880000),
    (19, 9, 11, 886881000),
    (19, 9, 12, 878871000),
    (19, 9, 13, 788781000),
    (19, 9, 14, 888672000),
    (19, 9, 15, 888870000),
    (19, 9, 16, 887871000),
    (19, 9, 17, 886872000),
    (19, 9, 18, 888780000),
    (19, 9, 0, 877882000),
    (19, 9, 1, 888682000),
    (19, 9, 2, 888880000),
    (19, 9, 3, 887881000),
    (19, 9, 4, 886882000),
    (19, 9, 5, 878872000),
    (19, 9, 6, 788782000),
    (19, 9, 7, 888673000),
    (19, 9, 8, 888871000),
    (19, 9, 9, 887872000),
    (19, 9, 10, 886873000),
    (19, 9, 11, 888781000),
    (19, 9, 12, 887782000),
    (19, 9, 13, 778882000),
    (19, 9, 14, 888862000),
    (19, 9, 15, 868882000),
    (19, 9, 16, 788881000),
    (19, 9, 17, 888772000),
    (19, 9, 18, 878881000),
    (23, 7, 0, 8587000),
    (23, 7, 1, 8884000),
    (23, 7, 2, 8767000),
    (23, 7, 3, 8857000),
    (23, 7, 4, 6877000),
    (23, 7, 5, 7588000),
    (23, 7, 6, 7885000),
    (23, 7, 7, 7768000),
    (23, 7, 8, 8686000),
    (23, 7, 9, 8776000),
    (23, 7, 10, 8866000),
    (23, 7, 11, 6886000),
    (23, 7, 12, 7866100),
    (23, 7, 13, 7687000),
    (23, 7, 14, 7777000),
    (23, 7, 15, 7867000),
    (23, 7, 16, 8785000),
    (23, 7, 17, 8875000),
    (23, 7, 18, 8758000),
    (23, 7, 19, 8848000),
    (23, 7, 20, 6868000),
    (23, 7, 21, 7786000),
    (23, 7, 22, 7876000),
    (23, 7, 0, 7867100),
    (23, 7, 1, 7688000),
    (23, 7, 2, 7778000),
    (23, 7, 3, 7868000),
    (23, 7, 4, 8786000),
    (23, 7, 5, 8876000),
    (23, 7, 6, 7786100),
    (23, 7, 7, 7876100),
    (23, 7, 8, 8587100),
    (23, 7, 9, 7787000),
    (23, 7, 10, 7877000),
    (23, 7, 11, 8588000),
    (23, 7, 12, 8885000),
    (23, 7, 13, 8768000),
    (23, 7, 14, 8858000),
    (23, 7, 15, 6878000),
    (23, 7, 16, 8686100),
    (23, 7, 17, 7886000),
    (23, 7, 18, 8866100),
    (23, 7, 19, 8687000),
    (23, 7, 20, 8777000),
    (23, 7, 21, 8867000),
    (23, 7, 22, 6887000),
    (23, 7, 0, 8886000),
    (23, 7, 1, 8686200),
    (23, 7, 2, 7886100),
    (23, 7, 3, 8866200),
    (23, 7, 4, 8687100),
    (23, 7, 5, 7887000),
    (23, 7, 6, 8867100),
    (23, 7, 7, 8688000),
    (23, 7, 8, 8778000),
    (23, 7, 9, 8868000),
    (23, 7, 10, 6888000),
    (23, 7, 11, 7868100),
    (23, 7, 12, 8786100),
    (23, 7, 13, 8876100),
    (23, 7, 14, 7786200),
    (23, 7, 15, 8787000),
    (23, 7, 16, 8877000),
    (23, 7, 17, 7787100),
    (23, 7, 18, 7877100),
    (23, 7, 19, 8588100),
    (23, 7, 20, 7788000),
    (23, 7, 21, 7878000),
    (23, 7, 22, 8858100),
    (23, 7, 0, 8787100),
    (23, 7, 1, 8877100),
    (23, 7, 2, 7787200),
    (23, 7, 3, 8788000),
    (23, 7, 4, 8878000),
    (23, 7, 5, 7788100),
    (23, 7, 6, 7878100),
    (23, 7, 7, 8858200),
    (23, 7, 8, 8886100),
    (23, 7, 9, 8686300),
    (23, 7, 10, 7886200),
    (23, 7, 11, 8887000),
    (23, 7, 12, 8687200),
    (23, 7, 13, 7887100),
    (23, 7, 14, 8867200),
    (23, 7, 15, 8688100),
    (23, 7, 16, 7888000),
    (23, 7, 17, 8868100),
    (23, 7, 18, 6888100),
    (23, 7, 19, 7868200),
    (23, 7, 20, 8786200),
    (23, 7, 21, 8876200),
    (23, 7, 22, 7786300),
    (23, 7, 0, 8688200),
    (23, 7, 1, 7888100),
    (23, 7, 2, 8868200),
    (23, 7, 3, 6888200),
    (23, 7, 4, 7868300),
    (23, 7, 5, 8786300),
    (23, 7, 6, 8876300),
    (23, 7, 7, 7786400),
    (23, 7, 8, 8787200),
    (23, 7, 9, 8877200),
    (23, 7, 10, 7787300),
    (23, 7, 11, 8788100),
    (23, 7, 12, 8878100),
    (23, 7, 13, 7788200),
    (23, 7, 14, 7878200),
    (23, 7, 15, 8858300),
    (23, 7, 16, 8886200),
    (23, 7, 17, 8686400),
    (23, 7, 18, 7886300),
    (23, 7, 19, 8887100),
    (23, 7, 20, 8687300),
    (23, 7, 21, 7887200),
    (23, 7, 22, 8888000),
    (23, 8, 0, 88862000),
    (23, 8, 1, 86882000),
    (23, 8, 2, 77864000),
    (23, 8, 3, 78782000),
    (23, 8, 4, 78872000),
    (23, 8, 5, 87863000),
    (23, 8, 6, 88781000),
    (23, 8, 7, 88871000),
    (23, 8, 8, 68882000),
    (23, 8, 9, 77873000),
    (23, 8, 10, 86864000),
    (23, 8, 11, 78881000),
    (23, 8, 12, 87872000),
    (23, 8, 13, 88583000),
    (23, 8, 14, 88880000),
    (23, 8, 15, 88763000),
    (23, 8, 16, 77882000),
    (23, 8, 17, 86873000),
    (23, 8, 18, 78683000),
    (23, 8, 19, 87881000),
    (23, 8, 20, 78863000),
    (23, 8, 21, 88682000),
    (23, 8, 22, 88772000),
    (23, 8, 0, 87873000),
    (23, 8, 1, 88584000),
    (23, 8, 2, 88881000),
    (23, 8, 3, 88764000),
    (23, 8, 4, 77883000),
    (23, 8, 5, 86874000),
    (23, 8, 6, 78684000),
    (23, 8, 7, 87882000),
    (23, 8, 8, 78864000),
    (23, 8, 9, 88683000),
    (23, 8, 10, 88773000),
    (23, 8, 11, 88863000),
    (23, 8, 12, 86883000),
    (23, 8, 13, 77865000),
    (23, 8, 14, 78783000),
    (23, 8, 15, 78873000),
    (23, 8, 16, 87864000),
    (23, 8, 17, 88782000),
    (23, 8, 18, 88872000),
    (23, 8, 19, 68883000),
    (23, 8, 20, 77874000),
    (23, 8, 21, 86865000),
    (23, 8, 22, 78882000),
    (23, 8, 0, 86884000),
    (23, 8, 1, 77866000),
    (23, 8, 2, 78784000),
    (23, 8, 3, 78874000),
    (23, 8, 4, 87865000),
    (23, 8, 5, 88783000),
    (23, 8, 6, 88873000),
    (23, 8, 7, 68884000),
    (23, 8, 8, 77875000),
    (23, 8, 9, 86866000),
    (23, 8, 10, 78883000),
    (23, 8, 11, 87874000),
    (23, 8, 12, 88585000),
    (23, 8, 13, 88882000),
    (23, 8, 14, 88765000),
    (23, 8, 15, 77884000),
    (23, 8, 16, 86875000),
    (23, 8, 17, 78685000),
    (23, 8, 18, 87883000),
    (23, 8, 19, 78865000),
    (23, 8, 20, 88684000),
    (23, 8, 21, 88774000),
    (23, 8, 22, 88864000),
    (23, 8, 0, 88586000),
    (23, 8, 1, 88883000),
    (23, 8, 2, 88766000),
    (23, 8, 3, 77885000),
    (23, 8, 4, 86876000),
    (23, 8, 5, 78686000),
    (23, 8, 6, 87884000),
    (23, 8, 7, 78866000),
    (23, 8, 8, 88685000),
    (23, 8, 9, 88775000),
    (23, 8, 10, 88865000),
    (23, 8, 11, 86885000),
    (23, 8, 12, 77867000),
    (23, 8, 13, 78785000),
    (23, 8, 14, 78875000),
    (23, 8, 15, 87866000),
    (23, 8, 16, 88784000),
    (23, 8, 17, 88874000),
    (23, 8, 18, 68885000),
    (23, 8, 19, 77876000),
    (23, 8, 20, 86867000),
    (23, 8, 21, 78884000),
    (23, 8, 22, 87875000),
    (23, 8, 0, 77868000),
    (23, 8, 1, 78786000),
    (23, 8, 2, 78876000),
    (23, 8, 3, 87867000),
    (23, 8, 4, 88785000),
    (23, 8, 5, 88875000),
    (23, 8, 6, 68886000),
    (23, 8, 7, 77877000),
    (23, 8, 8, 86868000),
    (23, 8, 9, 78885000),
    (23, 8, 10, 87876000),
    (23, 8, 11, 88587000),
    (23, 8, 12, 88884000),
    (23, 8, 13, 88767000),
    (23, 8, 14, 77886000),
    (23, 8, 15, 86877000),
    (23, 8, 16, 78687000),
    (23, 8, 17, 87885000),
    (23, 8, 18, 78867000),
    (23, 8, 19, 88686000),
    (23, 8, 20, 88776000),
    (23, 8, 21, 88866000),
    (23, 8, 22, 86886000),
    (23, 9, 0, 786870000),
    (23, 9, 1, 778680000),
    (23, 9, 2, 778770000),
    (23, 9, 3, 778860000),
    (23, 9, 4, 888660000),
    (23, 9, 5, 888750000),
    (23, 9, 6, 888840000),
    (23, 9, 7, 886860000),
    (23, 9, 8, 878670000),
    (23, 9, 9, 878760000),
    (23, 9, 10, 878850000),
    (23, 9, 11, 787860000),
    (23, 9, 12, 868680000),
    (23, 9, 13, 868770000),
    (23, 9, 14, 868860000),
    (23, 9, 15, 688860000),
    (23, 9, 16, 887670000),
    (23, 9, 17, 887760000),
    (23, 9, 18, 887850000),
    (23, 9, 19, 885870000),
    (23, 9, 20, 788670000),
    (23, 9, 21, 788760000),
    (23, 9, 22, 788850000),
    (23, 9, 0, 888760000),
    (23, 9, 1, 888850000),
    (23, 9, 2, 886870000),
    (23, 9, 3, 878680000),
    (23, 9, 4, 878770000),
    (23, 9, 5, 878860000),
    (23, 9, 6, 787870000),
    (23, 9, 7, 885871000),
    (23, 9, 8, 868780000),
    (23, 9, 9, 868870000),
    (23, 9, 10, 688870000),
    (23, 9, 11, 887680000),
    (23, 9, 12, 887770000),
    (23, 9, 13, 887860000),
    (23, 9, 14, 885880000),
    (23, 9, 15, 788680000),
    (23, 9, 16, 788770000),
    (23, 9, 17, 788860000),
    (23, 9, 18, 786880000),
    (23, 9, 19, 878671000),
    (23, 9, 20, 778780000),
    (23, 9, 21, 778870000),
    (23, 9, 22, 888670000),
    (23, 9, 0, 878870000),
    (23, 9, 1, 787880000),
    (23, 9, 2, 885881000),
    (23, 9, 3, 788681000),
    (23, 9, 4, 868880000),
    (23, 9, 5, 688880000),
    (23, 9, 6, 786881000),
    (23, 9, 7, 887780000),
    (23, 9, 8, 887870000),
    (23, 9, 9, 778871000),
    (23, 9, 10, 888671000),
    (23, 9, 11, 788780000),
    (23, 9, 12, 788870000),
    (23, 9, 13, 886871000),
    (23, 9, 14, 878681000),
    (23, 9, 15, 878771000),
    (23, 9, 16, 778880000),
    (23, 9, 17, 888680000),
    (23, 9, 18, 888770000),
    (23, 9, 19, 888860000),
    (23, 9, 20, 886880000),
    (23, 9, 21, 688871000),
    (23, 9, 22, 878780000),
    (23, 9, 0, 788871000),
    (23, 9, 1, 886872000),
    (23, 9, 2, 878682000),
    (23, 9, 3, 887880000),
    (23, 9, 4, 778881000),
    (23, 9, 5, 888681000),
    (23, 9, 6, 888771000),
    (23, 9, 7, 788880000),
    (23, 9, 8, 886881000),
    (23, 9, 9, 688872000),
    (23, 9, 10, 878781000),
    (23, 9, 11, 878871000),
    (23, 9, 12, 787881000),
    (23, 9, 13, 888780000),
    (23, 9, 14, 888870000),
    (23, 9, 15, 868881000),
    (23, 9, 16, 688881000),
    (23, 9, 17, 786882000),
    (23, 9, 18, 878880000),
    (23, 9, 19, 887871000),
    (23, 9, 20, 778872000),
    (23, 9, 21, 888672000),
    (23, 9, 22, 788781000),
    (23, 9, 0, 787882000),
    (23, 9, 1, 888781000),
    (23, 9, 2, 888871000),
    (23, 9, 3, 868882000),
    (23, 9, 4, 688882000),
    (23, 9, 5, 786883000),
    (23, 9, 6, 878881000),
    (23, 9, 7, 887872000),
    (23, 9, 8, 778873000),
    (23, 9, 9, 888880000),
    (23, 9, 10, 788782000),
    (23, 9, 11, 788872000),
    (23, 9, 12, 886873000),
    (23, 9, 13, 878683000),
    (23, 9, 14, 887881000),
    (23, 9, 15, 778882000),
    (23, 9, 16, 888682000),
    (23, 9, 17, 888772000),
    (23, 9, 18, 788881000),
    (23, 9, 19, 886882000),
    (23, 9, 20, 688873000),
    (23, 9, 21, 878782000),
    (23, 9, 22, 878872000)
  ]

def sigma10 (N : ℕ) : ℕ := (Nat.digits 10 N).sum

/-- Lemme du bloc bas (partie 2^a) : pour tout a >= 1 il existe
    B a a chiffres, tous dans {1,2}, divisible par 2^a, et
    sigma(B) <= 2a. Construction B_{a+1} = B_a + c.10^a,
    c dans {1,2} choisi par la parite de B_a / 2^a. -/
theorem lowBlock2 (a : ℕ) (ha : 1 ≤ a) :
    ∃ B : ℕ, 2 ^ a ∣ B ∧ (Nat.digits 10 B).length = a ∧
      (∀ d ∈ Nat.digits 10 B, d = 1 ∨ d = 2) ∧ sigma10 B ≤ 2 * a := by
  induction a with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨2, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num [Nat.digits, Nat.digitsAux]
      · intro d hd
        have : Nat.digits 10 2 = [2] := by norm_num [Nat.digits, Nat.digitsAux]
        rw [this] at hd
        simp at hd
        exact Or.inr hd
      · norm_num [sigma10, Nat.digits, Nat.digitsAux]
    · obtain ⟨B, hdiv, hlen, hdig, hsum⟩ := ih hk
      set t := B / 2 ^ k with ht
      set c := if t % 2 = 0 then 2 else 1 with hc
      have hcpos : 0 < c := by unfold c; split <;> norm_num
      have hclt : c < 10 := by unfold c; split <;> norm_num
      have hcmem : c = 1 ∨ c = 2 := by
        unfold c; split <;> simp
      have hBt : B = t * 2 ^ k := (Nat.div_mul_cancel hdiv).symm
      have h10k : (10 : ℕ) ^ k = 2 ^ k * 5 ^ k := by
        rw [← Nat.mul_pow]
      have hpar : 2 ∣ t + c * 5 ^ k := by
        unfold c
        split_ifs with hev
        · exact ⟨t / 2 + 5 ^ k, by omega⟩
        · have h5 : (5 : ℕ) ^ k % 2 = 1 := by
            have ho : Odd ((5 : ℕ) ^ k) := Odd.pow (by decide)
            exact Nat.odd_iff.mp ho
          have ht2 : t % 2 = 1 := by omega
          refine ⟨(t + 5 ^ k) / 2, ?_⟩
          omega
      have hd : Nat.digits 10 (B + c * 10 ^ k)
          = Nat.digits 10 B ++ [c] := by
        have h := Nat.digits_append_digits (b := 10) (m := c) (n := B)
          (by norm_num)
        rw [hlen] at h
        have hdc : Nat.digits 10 c = [c] :=
          Nat.digits_of_lt 10 c (by omega) hclt
        rw [hdc, mul_comm (10 ^ k) c] at h
        exact h.symm
      refine ⟨B + c * 10 ^ k, ?_, ?_, ?_, ?_⟩
      · rw [hBt, h10k]
        have hE : t * 2 ^ k + c * (2 ^ k * 5 ^ k)
            = 2 ^ k * (t + c * 5 ^ k) := by ring
        rw [hE]
        obtain ⟨w, hw⟩ := hpar
        rw [hw]
        exact ⟨w, by ring⟩
      · rw [hd, List.length_append, List.length_singleton, hlen]
      · rw [hd]
        intro d hd'
        rw [List.mem_append] at hd'
        rcases hd' with h1 | h2
        · exact hdig d h1
        · rw [List.mem_singleton] at h2
          rw [h2]; exact hcmem
      · rw [sigma10, hd, List.sum_append, List.sum_singleton]
        rw [sigma10] at hsum
        have hc2 : c ≤ 2 := by unfold c; split <;> norm_num
        omega


/-- Lemme du bloc bas (partie 5^b) : pour tout b >= 1 il existe
    B a b chiffres, tous dans {1,..,5}, divisible par 5^b, et
    sigma(B) <= 5b. Construction B_{b+1} = B_b + c.10^b,
    c dans {1,..,5} choisi modulo 5. -/
theorem lowBlock5 (b : ℕ) (hb : 1 ≤ b) :
    ∃ B : ℕ, 5 ^ b ∣ B ∧ (Nat.digits 10 B).length = b ∧
      (∀ d ∈ Nat.digits 10 B, 1 ≤ d ∧ d ≤ 5) ∧ sigma10 B ≤ 5 * b := by
  induction b with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨5, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num [Nat.digits, Nat.digitsAux]
      · intro d hd
        have : Nat.digits 10 5 = [5] := by norm_num [Nat.digits, Nat.digitsAux]
        rw [this] at hd; simp at hd; omega
      · norm_num [sigma10, Nat.digits, Nat.digitsAux]
    · obtain ⟨B, hdiv, hlen, hdig, hsum⟩ := ih hk
      set t := B / 5 ^ k with ht
      set w := t * 2 ^ (3 * k) % 5 with hw
      have hwlt : w < 5 := Nat.mod_lt _ (by norm_num)
      set c := 5 - w with hcdef
      have hcpos : 0 < c := by omega
      have hcle : c ≤ 5 := by omega
      have hclt : c < 10 := by omega
      have hBt : B = t * 5 ^ k := (Nat.div_mul_cancel hdiv).symm
      have h10k : (10 : ℕ) ^ k = 5 ^ k * 2 ^ k := by
        rw [← Nat.mul_pow]
      have h2k : (2 : ZMod 5) ^ (3 * k) * (2 : ZMod 5) ^ k = 1 := by
        rw [← pow_add]
        have : 3 * k + k = 4 * k := by ring
        rw [this, pow_mul]
        have h16 : ((2 : ZMod 5) ^ 4) = 1 := by decide
        rw [h16, one_pow]
      have hwz : (w : ZMod 5) = (t : ZMod 5) * (2 : ZMod 5) ^ (3 * k) := by
        have e : (w : ZMod 5) = ((t * 2 ^ (3 * k) : ℕ) : ZMod 5) := by
          rw [ZMod.natCast_eq_natCast_iff, hw]
          exact Nat.mod_modEq _ _
        calc (w : ZMod 5) = ((t * 2 ^ (3 * k) : ℕ) : ZMod 5) := e
        _ = (t : ZMod 5) * (2 : ZMod 5) ^ (3 * k) := by push_cast; rfl
      have hcz : (c : ZMod 5) = -(w : ZMod 5) := by
        have hcw : c + w = 5 := by omega
        have h2 := congrArg (Nat.cast : ℕ → ZMod 5) hcw
        push_cast at h2
        have h5z : (5 : ZMod 5) = 0 := by decide
        rw [h5z] at h2
        exact eq_neg_of_add_eq_zero_left h2
      have key : ((t : ZMod 5) + (c : ZMod 5) * (2 : ZMod 5) ^ k) = 0 := by
        calc (t : ZMod 5) + (c : ZMod 5) * (2 : ZMod 5) ^ k
            = (t : ZMod 5) + (-(w : ZMod 5)) * (2 : ZMod 5) ^ k := by
              rw [hcz]
          _ = (t : ZMod 5) - (t * (2 : ZMod 5) ^ (3 * k))
                * (2 : ZMod 5) ^ k := by rw [hwz]; ring
          _ = (t : ZMod 5) - t * ((2 : ZMod 5) ^ (3 * k)
                * (2 : ZMod 5) ^ k) := by ring
          _ = (t : ZMod 5) - t * 1 := by rw [h2k]
          _ = 0 := by ring
      have hpar : 5 ∣ t + c * 2 ^ k := by
        have h2 : ((t + c * 2 ^ k : ℕ) : ZMod 5) = 0 := by
          push_cast; exact key
        exact (CharP.cast_eq_zero_iff (ZMod 5) 5 _).mp h2
      have hd : Nat.digits 10 (B + c * 10 ^ k)
          = Nat.digits 10 B ++ [c] := by
        have h := Nat.digits_append_digits (b := 10) (m := c) (n := B)
          (by norm_num)
        rw [hlen] at h
        have hdc : Nat.digits 10 c = [c] :=
          Nat.digits_of_lt 10 c (by omega) hclt
        rw [hdc, mul_comm (10 ^ k) c] at h
        exact h.symm
      refine ⟨B + c * 10 ^ k, ?_, ?_, ?_, ?_⟩
      · rw [hBt, h10k]
        have hE : t * 5 ^ k + c * (5 ^ k * 2 ^ k)
            = 5 ^ k * (t + c * 2 ^ k) := by ring
        rw [hE]
        obtain ⟨w2, hw2⟩ := hpar
        rw [hw2]
        exact ⟨w2, by ring⟩
      · rw [hd, List.length_append, List.length_singleton, hlen]
      · rw [hd]
        intro d hd'
        rw [List.mem_append] at hd'
        rcases hd' with h1 | h2
        · exact hdig d h1
        · rw [List.mem_singleton] at h2
          rw [h2]; omega
      · rw [sigma10, hd, List.sum_append, List.sum_singleton]
        rw [sigma10] at hsum
        omega

/-- La grille d echange : x = d1 + 11 d2, d_i in [-4,4],
    |d1+d2| <= 4, x =/= 0. |X| = 60 (decidable). -/
def Xgrid : List ℤ :=
  (((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4).product
    ((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4)).filterMap
    fun p =>
      if -4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 4 ∧ p.1 + 11 * p.2 ≠ 0
      then some (p.1 + 11 * p.2) else none

/-- les elements {2,5}-smooth de X : 16 signes. -/
theorem Xsmooth25_sub : ∀ x ∈ Xsmooth25, x ∈ Xgrid := by decide

theorem Xsmooth235_sub : ∀ x ∈ Xsmooth235, x ∈ Xgrid := by decide

/-- Concatenation sans retenue : N = B + 10^d.H avec
    d = nb de chiffres de B (B /= 0) se decompose en
    digits N = digits B ++ digits H. -/
theorem digits_concat (B H : ℕ) (hB : B ≠ 0) :
    Nat.digits 10 (B + 10 ^ (Nat.digits 10 B).length * H)
      = Nat.digits 10 B ++ Nat.digits 10 H := by
  have h := Nat.digits_append_digits (b := 10) (m := H) (n := B)
    (by norm_num)
  exact h.symm

/-- sigma se distribue sur la concatenation. -/
theorem sigma_concat (B H : ℕ) (hB : B ≠ 0) :
    sigma10 (B + 10 ^ (Nat.digits 10 B).length * H)
      = sigma10 B + sigma10 H := by
  rw [sigma10, digits_concat B H hB, List.sum_append]; rfl

/-- Theoreme de Chowla (1935) : dans Z/k, si 0 in B et tout
    autre element de B est une unite, alors
    |A+B| >= min(k, |A|+|B|-1). Preuve e-transform. -/
theorem chowla (k : ℕ) [NeZero k] (A B : Finset (ZMod k))
    (hA : A.Nonempty) (h0 : 0 ∈ B) (hu : ∀ b ∈ B, b = 0 ∨ IsUnit b) :
    min k (A.card + B.card - 1) ≤ (A + B).card := by
  suffices H : ∀ n : ℕ, ∀ (A B : Finset (ZMod k)), B.card ≤ n →
      A.Nonempty → 0 ∈ B → (∀ b ∈ B, b = 0 ∨ IsUnit b) →
      min k (A.card + B.card - 1) ≤ (A + B).card by
    exact H B.card A B le_rfl hA h0 hu
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro A B hBn hA h0 hu
  -- cas trivial : A + B atteint deja la taille du groupe
  rcases lt_or_ge (A + B).card k with hcase | hcase
  swap
  · exact le_trans (min_le_left _ _) hcase
  by_cases hfull : ∃ a0 ∈ A, ∃ b0 ∈ B, b0 ≠ 0 ∧ a0 + b0 ∉ A
  · -- etape e-transform : on fait decroitre |B|
    obtain ⟨a0, ha0, b0, hb0, hb0n, hnotin⟩ := hfull
    set T := Finset.addDysonETransform a0 (A, B) with hTdef
    have hTcard := Finset.addDysonETransform.card a0 (A, B)
    have hTsub := Finset.addDysonETransform.subset a0 (A, B)
    have hT1 : T.1 = A ∪ (a0 +ᵥ B) := rfl
    have hT2 : T.2 = B ∩ ((-a0) +ᵥ A) := rfl
    have h0' : (0 : ZMod k) ∈ T.2 := by
      rw [hT2, Finset.mem_inter]
      refine ⟨h0, ?_⟩
      change 0 ∈ A.image (fun x => -a0 +ᵥ x)
      rw [Finset.mem_image]
      exact ⟨a0, ha0, by simp⟩
    have hb0' : b0 ∉ T.2 := by
      rw [hT2, Finset.mem_inter]
      rintro ⟨-, h⟩
      change b0 ∈ A.image (fun x => -a0 +ᵥ x) at h
      rw [Finset.mem_image] at h
      obtain ⟨a, ha, hva⟩ := h
      apply hnotin
      have haeq : a = a0 + b0 := by
        rw [vadd_eq_add] at hva
        have hc : a0 + (-a0 + a) = a := by
          rw [← add_assoc, add_neg_cancel, zero_add]
        rw [hva] at hc; rw [← hc]
      rwa [← haeq]
    have hB'lt : T.2.card < B.card := by
      apply Finset.card_lt_card
      exact ⟨hT2.symm ▸ Finset.inter_subset_left, fun h => hb0' (h hb0)⟩
    have hu' : ∀ b ∈ T.2, b = 0 ∨ IsUnit b := fun b hb =>
      hu b ((Finset.mem_inter.mp (hT2 ▸ hb)).1)
    have hA' : T.1.Nonempty :=
      hA.mono (hT1.symm ▸ Finset.subset_union_left)
    have ih' := ih T.2.card (lt_of_lt_of_le hB'lt hBn) T.1 T.2 le_rfl hA' h0' hu'
    calc min k (A.card + B.card - 1)
        = min k (T.1.card + T.2.card - 1) := by rw [hTcard]
      _ ≤ (T.1 + T.2).card := ih'
      _ ≤ (A + B).card := Finset.card_mono hTsub
  · -- pas de (a0,b0) : A est periodique - contradiction avec cardinal
    push_neg at hfull
    by_cases hB1 : B.card ≤ 1
    · -- B = {0} : A + B = A
      have hBeq : B = {0} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨h0, fun x hx =>
          Finset.card_le_one.mp hB1 x hx 0 h0⟩
      rw [hBeq]
      simp
    · -- B >= 2 : prendre b0 ≠ 0 unite → A + b0 = A → k | |A| → A = univ
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
        (by omega : 1 < B.card)
      obtain ⟨b0, hb0, hb0n⟩ : ∃ b0 ∈ B, b0 ≠ 0 := by
        rcases eq_or_ne x 0 with hx0 | hx0
        · exact ⟨y, hy, fun h => hxy (hx0.trans h.symm)⟩
        · exact ⟨x, hx, hx0⟩
      have hAbs : A.image (· + b0) ⊆ A := by
        intro x hx
        rw [Finset.mem_image] at hx; obtain ⟨a, ha, rfl⟩ := hx
        exact hfull a ha b0 hb0 hb0n
      have hinj : Set.InjOn (· + b0) A :=
        Set.injOn_of_injective (fun x y h => add_right_cancel h)
      have heq : A.image (· + b0) = A :=
        Finset.eq_of_subset_of_card_le hAbs
          (by rw [Finset.card_image_of_injOn hinj])
      have hsum : ∑ x ∈ A, x = ∑ a ∈ A, (a + b0) := by
        have h := Finset.sum_image (s := A) (g := (· + b0)) (f := id) hinj
        rw [heq] at h; simpa using h
      rw [Finset.sum_add_distrib, Finset.sum_const] at hsum
      have h0b : A.card • b0 = 0 :=
        add_left_cancel (show ∑ x ∈ A, x + A.card • b0 = ∑ x ∈ A, x + 0
          from by rw [add_zero]; exact hsum.symm)
      rw [nsmul_eq_mul] at h0b
      have hu' := hu b0 hb0
      rcases hu' with hb0z | hb0u
      · exact absurd hb0z hb0n
      have hA0 : (A.card : ZMod k) = 0 :=
        (IsUnit.mul_left_eq_zero hb0u).mp h0b
      have hkdvd : k ∣ A.card :=
        (CharP.cast_eq_zero_iff (ZMod k) k A.card).mp hA0
      have hAcard : A.card = k := by
        have hpos : 0 < A.card := Finset.card_pos.mpr hA
        have hle : A.card ≤ k := by
          have := Finset.card_le_univ A
          rwa [ZMod.card] at this
        have hkle : k ≤ A.card := Nat.le_of_dvd hpos hkdvd
        omega
      have hAuniv : A = Finset.univ := Finset.eq_univ_of_card A (by
        rw [hAcard, ZMod.card])
      have : (A + B).card = k := by
        have hu2 : (A + B) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro x
          rw [hAuniv]
          exact Finset.mem_add.mpr ⟨x, Finset.mem_univ x, 0, h0, add_zero x⟩
        rw [hu2, Finset.card_univ, ZMod.card]
      omega

/-- La fibre : H = somme_e (1 + u_e) . 10^e pour e < L,
    representee comme ofDigits de la liste des chiffres. -/
def fibre (u : ℕ → ℕ) (L : ℕ) : ℕ :=
  Nat.ofDigits 10 ((List.range L).map fun e => 1 + u e)

/-- Recurrence de la fibre : fibre u (L+1) = fibre u L +
    10^L . (1 + u L). -/
theorem fibre_succ (u : ℕ → ℕ) (L : ℕ) :
    fibre u (L + 1) = fibre u L + 10 ^ L * (1 + u L) := by
  rw [fibre, List.range_succ, List.map_append, List.map_singleton,
      Nat.ofDigits_append]
  simp [fibre]

/-- Valeur de la fibre : somme_e (1 + u_e) . 10^e. -/
theorem fibre_val (u : ℕ → ℕ) (L : ℕ) :
    fibre u L = ∑ e ∈ Finset.range L, (1 + u e) * 10 ^ e := by
  induction' L with L ih
  · simp [fibre]
  · rw [fibre_succ, ih, Finset.sum_range_succ]
    ring

/-- Delta de la fibre : v = u + D (sur Z) change la valeur
    de somme_e D_e . 10^e. -/
theorem fibre_delta (u v : ℕ → ℕ) (D : ℕ → ℤ) (L : ℕ)
    (hd : ∀ e, (v e : ℤ) = u e + D e) :
    (fibre v L : ℤ) = (fibre u L : ℤ) +
      ∑ e ∈ Finset.range L, D e * (10 : ℤ) ^ e := by
  rw [fibre_val u, fibre_val v]; push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [hd e]; ring

/-- Deltas equilibres sur s triplets disjoints {3j+3,3j+4,
    3j+5} (j < s) : la fibre change de la somme des
    9.10^{3(j+1)}.(D(3j+4) + 11 D(3j+5)). -/
theorem fibre_stages_delta (u v : ℕ → ℕ) (D : ℕ → ℤ) (L s : ℕ)
    (hL : 3 * s + 3 ≤ L)
    (hd : ∀ e, (v e : ℤ) = u e + D e)
    (hT : ∀ e, e ∉ (Finset.range s).biUnion
        (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) → D e = 0)
    (hbal : ∀ j < s,
        D (3*j+3) + D (3*j+4) + D (3*j+5) = 0) :
    (fibre v L : ℤ) = (fibre u L : ℤ) + ∑ j ∈ Finset.range s,
      9 * 10 ^ (3*(j+1)) * (D (3*j+4) + 11 * D (3*j+5)) := by
  rw [fibre_delta u v D L hd]; congr 1
  have hsub : (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) ⊆
      Finset.range L := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxt⟩ := hx
    rw [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl <;> omega
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ)
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) := by
    intro j _ j' _ hjj'
    rw [Function.onFun]
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with h | h | h <;> omega
  rw [← Finset.sum_subset hsub (fun e _ he => by
    have hde : D e = 0 := hT e he
    rw [hde]; simp)]
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hi1 : 3*j+3 ∉ ({3*j+4, 3*j+5} : Finset ℕ) := by simp
  have hi2 : 3*j+4 ∉ ({3*j+5} : Finset ℕ) := by simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have h0 : D (3*j+3) = -(D (3*j+4) + D (3*j+5)) := by
    have := hbal j hj; omega
  have e1 : (10 : ℤ) ^ (3*j+4) = 10 * 10 ^ (3*j+3) :=
    pow_succ' 10 (3*j+3)
  have e2 : (10 : ℤ) ^ (3*j+5) = 10 * 10 ^ (3*j+4) :=
    pow_succ' 10 (3*j+4)
  have e3 : 3*(j+1) = 3*j+3 := by ring
  rw [h0, e2, e1, e3]; ring

/-- Les chiffres de la fibre sont exactement les 1 + u_e
    (des que u_e <= 8). -/
theorem fibre_digits (u : ℕ → ℕ) (L : ℕ) (hu : ∀ e < L, u e ≤ 8) :
    Nat.digits 10 (fibre u L) = (List.range L).map fun e => 1 + u e := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_map] at hd
    obtain ⟨e, he, rfl⟩ := hd
    have := hu e (List.mem_range.mp he)
    omega
  · intro hne
    have hL : 0 < L := by
      rcases Nat.eq_zero_or_pos L with rfl | h
      · simp at hne
      · exact h
    have : ((List.range L).map fun e => 1 + u e).getLast hne
        = 1 + u (L - 1) := by
      simp [List.getLast_map, List.getLast_range (by simpa using hL.ne')]
    rw [this]; omega

/-- sigma(H) = L + somme u_e ; en particulier = L + K si
    somme u_e = K. -/
theorem fibre_sigma (u : ℕ → ℕ) (L : ℕ) (hu : ∀ e < L, u e ≤ 8) :
    sigma10 (fibre u L) = L + ((List.range L).map u).sum := by
  rw [sigma10, fibre_digits u L hu]
  have hgen : ∀ l : List ℕ,
      ((l.map fun e => 1 + u e).sum) = l.length + (l.map u).sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
          List.length_cons, ih]; omega
  rw [hgen, List.length_range]

/-- Reduction mod R : si R | 10^d et R | B, alors
    R | B + 10^d.H (le bloc bas absorbe la fibre). -/
theorem dvd_concat_base (R B H d : ℕ) (hR10 : R ∣ 10 ^ d)
    (hRB : R ∣ B) : R ∣ B + 10 ^ d * H :=
  dvd_add hRB (dvd_mul_of_dvd_left hR10 H)

/-- Le scalaire 9/g est premier avec M = m/g (g = gcd(9,m)) :
    c'est ce qui rend chaque facteur d'etage une unite mod M. -/
theorem scalar_unit (m : ℕ) :
    Nat.Coprime (9 / Nat.gcd 9 m) (m / Nat.gcd 9 m) :=
  Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left m (by norm_num))

/-- L'ensemble d'etage B* i dans ZMod M : {0} union
    {(9/g).10^{3i}.x mod M} pour x dans la liste d'unites. -/
def stageSet (M i g : ℕ) (xs : List ℤ) : Finset (ZMod M) :=
  {0} ∪ (xs.toFinset.image fun (x : ℤ) =>
    ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M))

theorem zero_mem_stageSet (M i g : ℕ) (xs : List ℤ) :
    (0 : ZMod M) ∈ stageSet M i g xs :=
  Finset.mem_union_left _ (Finset.mem_singleton_self 0)

/-- Les elements non nuls d'un etage sont des unites, des que
    9/g, 10 et chaque x de la liste sont des unites mod M. -/
theorem stageSet_units (M i g : ℕ) (xs : List ℤ)
    (hsc : IsUnit ((9 / g : ℕ) : ZMod M))
    (h10 : IsUnit ((10 : ℕ) : ZMod M))
    (hx : ∀ x ∈ xs, IsUnit (x : ZMod M)) :
    ∀ b ∈ stageSet M i g xs, b = 0 ∨ IsUnit b := by
  intro b hb
  rw [stageSet, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image] at hb
  rcases hb with rfl | ⟨x, hxs, rfl⟩
  · exact Or.inl rfl
  · right
    exact ((hsc.mul (h10.pow _)).mul (hx x (List.mem_toFinset.mp hxs)))

/-- Cardinal d'un etage : pour M > 184, les x distincts
    donnent des residus distincts (l'injectivite vient du cast
    et de la multiplication par l'unite), et 0 n'est pas
    atteint, donc |B*_i| = |xs| + 1. -/
theorem stageSet_card (M i g : ℕ) (xs : List ℤ)
    (hM : 184 < M) (hsc : IsUnit ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M))
    (hnd : xs.Nodup) (hxb : ∀ x ∈ xs, |x| ≤ 92)
    (hx0 : ∀ x ∈ xs, x ≠ 0) :
    (stageSet M i g xs).card = xs.length + 1 := by
  have hc0 : ∀ x ∈ xs, (x : ZMod M) ≠ 0 := by
    intro x hx hxe
    rw [CharP.intCast_eq_zero_iff (ZMod M) M] at hxe
    have h2 : M ∣ x.natAbs := Int.natCast_dvd.mp hxe
    have h3 : x.natAbs ≤ 92 := by
      have h := hxb x hx
      rw [← Int.natCast_natAbs x] at h
      exact_mod_cast h
    have h4 : x.natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    exact hx0 x hx (Int.natAbs_eq_zero.mp h4)
  have hinj : Set.InjOn (fun (x : ℤ) =>
      ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M))
      (↑xs.toFinset : Set ℤ) := by
    intro x hx y hy hxy
    have hxy' : (x : ZMod M) = (y : ZMod M) :=
      hsc.mul_right_inj.mp hxy
    rw [Finset.mem_coe, List.mem_toFinset] at hx hy
    rw [ZMod.intCast_eq_intCast_iff] at hxy'
    have hdvd : (M : ℤ) ∣ (y - x) := Int.modEq_iff_dvd.mp hxy'
    have h2 : M ∣ (y - x).natAbs := Int.natCast_dvd.mp hdvd
    have hlt : (y - x).natAbs < M := by
      have h1 := hxb x hx; have h2' := hxb y hy
      have hb : |y - x| ≤ (184 : ℤ) := by
        have hx' := abs_le.mp h1
        have hy' := abs_le.mp h2'
        exact abs_le.mpr ⟨by omega, by omega⟩
      have hlt' : (|y - x| : ℤ) < M :=
        lt_of_le_of_lt hb (by exact_mod_cast hM)
      rw [← Int.natCast_natAbs] at hlt'
      exact_mod_cast hlt'
    have h0 : (y - x).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt h2 hlt
    exact (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0)).symm
  have h0im : (0 : ZMod M) ∉ xs.toFinset.image fun (x : ℤ) =>
      ((9 / g : ℕ) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M) := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hxe⟩ := h
    have hx' : x ∈ xs := List.mem_toFinset.mp hx
    have : (x : ZMod M) = 0 := hsc.mul_right_eq_zero.mp hxe
    exact hc0 x hx' this
  rw [stageSet, Finset.singleton_union,
      Finset.card_insert_of_notMem h0im,
      Finset.card_image_of_injOn hinj,
      List.toFinset_card_of_nodup hnd]

/-- Tout element de la liste 16 ({2,5}-smooth) a sa valeur
    absolue divisant 160 ; pour M coprime a 10 c'est donc une
    unite mod M. -/
theorem xunit25 (M : ℕ) (hM : Nat.Coprime M 10) :
    ∀ x ∈ Xsmooth25, IsUnit (x : ZMod M) := by
  have h160 : (160 : ℕ).Coprime M := by
    have h10 : (10 : ℕ).Coprime M := Nat.coprime_comm.mp hM
    have h2 : (2 : ℕ).Coprime M := h10.coprime_dvd_left (by norm_num)
    have h5 : (5 : ℕ).Coprime M := h10.coprime_dvd_left (by norm_num)
    have h25 : (2 ^ 5 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 5 by norm_num) 2 M).mpr h2
    rw [show (160 : ℕ) = 2 ^ 5 * 5 by norm_num]
    exact (Nat.coprime_mul_iff_left).mpr ⟨h25, h5⟩
  intro x hx
  have hxd : x.natAbs ∣ 160 := by fin_cases hx <;> decide
  have hxu : IsUnit ((x.natAbs : ℕ) : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact h160.coprime_dvd_left hxd
  rcases Int.natAbs_eq x with h | h
  · rw [h, Int.cast_natCast]; exact hxu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hxu.neg

/-- Tout element de la liste 28 ({2,3,5}-smooth) a sa valeur
    absolue divisant 2880 ; pour M coprime a 30 c'est une
    unite mod M. -/
theorem xunit235 (M : ℕ) (hM : Nat.Coprime M 30) :
    ∀ x ∈ Xsmooth235, IsUnit (x : ZMod M) := by
  have h2880 : (2880 : ℕ).Coprime M := by
    have h30 : (30 : ℕ).Coprime M := Nat.coprime_comm.mp hM
    have h2 : (2 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h3 : (3 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h5 : (5 : ℕ).Coprime M := h30.coprime_dvd_left (by norm_num)
    have h26 : (2 ^ 6 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 6 by norm_num) 2 M).mpr h2
    have h32 : (3 ^ 2 : ℕ).Coprime M :=
      (Nat.coprime_pow_left_iff (show 0 < 2 by norm_num) 3 M).mpr h3
    rw [show (2880 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 by norm_num]
    exact (Nat.coprime_mul_iff_left).mpr
      ⟨(Nat.coprime_mul_iff_left).mpr ⟨h26, h32⟩, h5⟩
  intro x hx
  have hxd : x.natAbs ∣ 2880 := by fin_cases hx <;> decide
  have hxu : IsUnit ((x.natAbs : ℕ) : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact h2880.coprime_dvd_left hxd
  rcases Int.natAbs_eq x with h | h
  · rw [h, Int.cast_natCast]; exact hxu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hxu.neg

/-- Appartenance a une somme d'etages : x in sum_j B j ssi il
    existe des choix f j in B j dont x est la somme. -/
theorem mem_sum_range {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (B : ℕ → Finset α) (x : α) :
    ∀ s : ℕ, x ∈ ∑ j ∈ Finset.range s, B j ↔
      ∃ f : ℕ → α, (∀ j < s, f j ∈ B j) ∧
        x = ∑ j ∈ Finset.range s, f j := by
  intro s
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨f, hf, rfl⟩ := (ih a).mp ha
      refine ⟨Function.update f s b, fun j hj => ?_, ?_⟩
      · rcases Nat.lt_or_ge j s with h | h
        · rw [Function.update_of_ne (Nat.ne_of_lt h)]
          exact hf j h
        · have hjs : j = s := by omega
          subst hjs
          rw [Function.update_self]
          exact hb
      · rw [Finset.sum_range_succ, Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (by
          rw [Finset.mem_range] at hj; omega)]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨∑ j ∈ Finset.range s, f j, ?_, f s, hf s (by simp),
        by rw [Finset.sum_range_succ]⟩
      exact (ih _).mpr ⟨f, fun j hj => hf j (by omega), rfl⟩

/-- Inversion de la grille : x in Xgrid ssi x = d1 + 11.d2
    avec (d1,d2) in [-4,4]^2, |d1+d2| <= 4, x /= 0.
    Le d0 equilibrant est alors -(d1+d2) in [-4,4]. -/
theorem mem_XR_iff (d : ℤ) :
    d ∈ ((List.range 9).map fun (i : ℕ) => (i : ℤ) - 4) ↔
      -4 ≤ d ∧ d ≤ 4 := by
  constructor
  · intro h
    fin_cases h <;> decide
  · intro ⟨h1, h2⟩
    interval_cases d <;> decide

theorem Xgrid_mem_iff (x : ℤ) :
    x ∈ Xgrid ↔ ∃ d1 d2 : ℤ, -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧
      d2 ≤ 4 ∧ -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧
      x = d1 + 11 * d2 ∧ x ≠ 0 := by
  constructor
  · intro hx
    unfold Xgrid at hx
    rw [List.mem_filterMap] at hx
    obtain ⟨⟨d1, d2⟩, hp, hopt⟩ := hx
    dsimp only at hopt
    replace hp : (d1, d2) ∈
        ((List.range 9).map fun i => (i : ℤ) - 4) ×ˢ
        ((List.range 9).map fun i => (i : ℤ) - 4) := hp
    rw [List.mem_product] at hp
    replace hp : d1 ∈
        (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) ∧
        d2 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) := hp
    rw [mem_XR_iff, mem_XR_iff] at hp
    split at hopt
    · next hc =>
      obtain ⟨h1, h2, h3⟩ := hc
      injection hopt with hopt
      exact ⟨d1, d2, hp.1.1, hp.1.2, hp.2.1, hp.2.2, h1, h2,
        hopt.symm, hopt ▸ h3⟩
    · contradiction
  · rintro ⟨d1, d2, hd1a, hd1b, hd2a, hd2b, h1, h2, rfl, h3⟩
    unfold Xgrid
    rw [List.mem_filterMap]
    refine ⟨⟨d1, d2⟩, ?_, ?_⟩
    · show (d1, d2) ∈
        ((List.range 9).map fun i => (i : ℤ) - 4) ×ˢ
        ((List.range 9).map fun i => (i : ℤ) - 4)
      rw [List.mem_product]
      show d1 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4) ∧
        d2 ∈ (List.range 9).map (fun i : ℕ => (i : ℤ) - 4)
      rw [mem_XR_iff, mem_XR_iff]
      exact ⟨⟨hd1a, hd1b⟩, ⟨hd2a, hd2b⟩⟩
    · dsimp only
      rw [if_pos ⟨h1, h2, h3⟩]

theorem zero_mem_sum_range {α : Type*} [AddCommMonoid α]
    [DecidableEq α] (s : ℕ) (B : ℕ → Finset α)
    (h0 : ∀ j, (0 : α) ∈ B j) :
    (0 : α) ∈ ∑ j ∈ Finset.range s, B j := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    simpa using Finset.add_mem_add ih (h0 s)

/-- Iteration de Chowla : si chaque B_j contient 0, que tout
    element non nul de B_j est une unite, et que |B_j| >= q+1,
    alors la somme des s premiers etages a cardinal >=
    min(k, s*q+1) (k = card de l'anneau). -/
theorem sumset_stages (k q : ℕ) [NeZero k]
    (B : ℕ → Finset (ZMod k)) (h0 : ∀ j, (0 : ZMod k) ∈ B j)
    (hu : ∀ j, ∀ x ∈ B j, x ≠ 0 → IsUnit x)
    (hq : ∀ j, q + 1 ≤ (B j).card) (s : ℕ) :
    min k (s * q + 1) ≤
      (∑ j ∈ Finset.range s, B j).card := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hle : (∑ j ∈ Finset.range s, B j).card ≤
        ((∑ j ∈ Finset.range s, B j) + B s).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' : x = x + (0 : ZMod k) := (add_zero x).symm
      rw [hx']
      exact Finset.add_mem_add hx (h0 s)
    have hchow := chowla k (∑ j ∈ Finset.range s, B j) (B s)
      ⟨(0 : ZMod k), zero_mem_sum_range _ _ h0⟩ (h0 s)
      (fun x hx => (eq_or_ne x 0).elim Or.inl
        (fun hne => Or.inr (hu s x hx hne)))
    have hcard : min k ((∑ j ∈ Finset.range s, B j).card +
        (B s).card - 1) ≤
        ((∑ j ∈ Finset.range s, B j) + B s).card := hchow
    rcases lt_or_ge (s * q + 1) k with hkc | hkc
    · have hSk : s * q + 1 ≤
          (∑ j ∈ Finset.range s, B j).card := by
        rwa [min_eq_right (le_of_lt hkc)] at ih
      calc min k ((s + 1) * q + 1)
          ≤ min k ((∑ j ∈ Finset.range s, B j).card +
              (B s).card - 1) := by
            apply min_le_min_left k
            have hB : q + 1 ≤ (B s).card := hq s
            have h0S : 0 < (∑ j ∈ Finset.range s, B j).card :=
              Finset.card_pos.mpr
                ⟨(0 : ZMod k), zero_mem_sum_range _ _ h0⟩
            rw [show (s + 1) * q + 1 = s * q + q + 1 from by ring]
            omega
        _ ≤ ((∑ j ∈ Finset.range s, B j) + B s).card := hcard
    · -- la somme partielle atteint deja l'univers
      have hSk : k ≤ (∑ j ∈ Finset.range s, B j).card := by
        rwa [min_eq_left hkc] at ih
      have huniv : (∑ j ∈ Finset.range s, B j) =
          Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [ZMod.card]
        refine le_antisymm ?_ hSk
        have h := Finset.card_le_univ
          (∑ j ∈ Finset.range s, B j)
        rwa [ZMod.card] at h
      have hsub : (Finset.univ : Finset (ZMod k)) ⊆
          (∑ j ∈ Finset.range s, B j) + B s := by
        rw [← huniv]
        intro x hx
        simpa using Finset.add_mem_add hx (h0 s)
      calc min k ((s + 1) * q + 1) ≤ k := min_le_left _ _
        _ = (Finset.univ : Finset (ZMod k)).card := by
            rw [Finset.card_univ, ZMod.card]
        _ ≤ ((∑ j ∈ Finset.range s, B j) + B s).card :=
            Finset.card_le_card hsub

/-- Couverture par les etages : si chaque etage a >= q+1
    elements (0 inclus) et s.q >= M-1, la somme des s etages
    est tout ZMod M. C'est sumset_stages applique aux B*_j. -/
theorem stage_cover (M g q s : ℕ) [NeZero M] (xs : List ℤ)
    (hM : 184 < M)
    (hsc : IsUnit ((9 / g : ℕ) : ZMod M))
    (h10 : IsUnit ((10 : ℕ) : ZMod M))
    (hxu : ∀ x ∈ xs, IsUnit (x : ZMod M))
    (hnd : xs.Nodup) (hxb : ∀ x ∈ xs, |x| ≤ 92)
    (hx0 : ∀ x ∈ xs, x ≠ 0)
    (hq : q ≤ xs.length) (hs : M ≤ s * q + 1) :
    ∑ j ∈ Finset.range s, stageSet M (j + 1) g xs = Finset.univ := by
  have hcard : ∀ j, (stageSet M (j + 1) g xs).card =
      xs.length + 1 := by
    intro j
    apply stageSet_card M (j + 1) g xs hM _ hnd hxb hx0
    push_cast
    exact hsc.mul (h10.pow _)
  have hsum := sumset_stages M q
    (fun j => stageSet M (j + 1) g xs)
    (fun j => zero_mem_stageSet _ _ _ _)
    (fun j x hx hx0 =>
      (stageSet_units _ _ _ _ hsc h10 hxu x hx).resolve_left hx0)
    (fun j => by rw [hcard j]; omega)
    s
  rw [min_eq_left hs] at hsum
  have hle2 : (∑ j ∈ Finset.range s, stageSet M (j + 1) g xs).card
      ≤ M := by
    have h := Finset.card_le_univ
      (∑ j ∈ Finset.range s, stageSet M (j + 1) g xs)
    rwa [ZMod.card] at h
  have hfc : Fintype.card (ZMod M) = M := ZMod.card M
  exact Finset.eq_univ_of_card _ (by omega)

/-- Fonction de base des fibres : u = 4 partout, plus 1 sur r0
    positions libres - les positions 0,1,2 tant que e < r0, et
    3s+3 quand r0 = 4. Les triplets d'echange {3j+3,3j+4,3j+5},
    j < s, ne rencontrent jamais ces positions libres. -/
def ubase (s r0 : ℕ) (e : ℕ) : ℕ :=
  if (e < 3 ∧ e < r0) ∨ (e = 3 * s + 3 ∧ r0 = 4) then 5 else 4

theorem ubase_le (s r0 : ℕ) (hr0 : r0 ≤ 4) (e : ℕ) :
    ubase s r0 e ≤ 8 := by
  rw [ubase]; split_ifs <;> omega

/-- Les triplets d'echange portent la valeur de base 4 :
    indispensable pour que les offsets d in [-4,4] gardent
    u dans [0,8]. -/
theorem ubase_triple (s r0 : ℕ) (j e : ℕ) (hj : j < s)
    (he : e ∈ ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) :
    ubase s r0 e = 4 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rw [ubase, if_neg]
  push_neg
  refine ⟨by omega, fun h => ?_⟩
  rcases he with rfl | rfl | rfl <;> omega

/-- Somme de la base auxiliaire : la somme vaut 4L plus le
    nombre de positions libres presentes dans [0,L). -/
theorem ubase_sum_aux (s r0 L : ℕ) :
    ((List.range L).map (ubase s r0)).sum = 4 * L +
      (if 0 < L ∧ 0 < r0 then 1 else 0) +
      (if 1 < L ∧ 1 < r0 then 1 else 0) +
      (if 2 < L ∧ 2 < r0 then 1 else 0) +
      (if 3 * s + 3 < L ∧ r0 = 4 then 1 else 0) := by
  induction' L with L ih
  · simp
  · rw [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ih]
    dsimp [ubase]
    split_ifs <;> omega

/-- Somme de la base : Σ_{e<L} ubase e = 4L + r0 des que la
    position libre haute 3s+3 est dans la fibre (L >= 3s+4). -/
theorem ubase_sum (s r0 L : ℕ) (hr0 : r0 ≤ 4)
    (hL : 3 * s + 4 ≤ L) :
    ((List.range L).map (ubase s r0)).sum = 4 * L + r0 := by
  rw [ubase_sum_aux]
  split_ifs <;> omega

/-- Somme des deltas portes par les s triplets equilibres :
    elle est nulle (chaque triplet somme a 0). -/
theorem sum_stages_zero (D : ℕ → ℤ) (L s : ℕ)
    (hL : 3 * s + 3 ≤ L)
    (hT : ∀ e, e ∉ (Finset.range s).biUnion
        (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) → D e = 0)
    (hbal : ∀ j < s,
        D (3*j+3) + D (3*j+4) + D (3*j+5) = 0) :
    ∑ e ∈ Finset.range L, D e = 0 := by
  have hsub : (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) ⊆
      Finset.range L := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨j, hj, hxt⟩ := hx
    rw [Finset.mem_range] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxt
    rcases hxt with rfl | rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub (fun e _ he => by
    have hde : D e = 0 := hT e he
    rw [hde])]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ)
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) := by
    intro j _ j' _ hjj'
    rw [Function.onFun]
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with h | h | h <;> omega
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  have hi1 : 3*j+3 ∉ ({3*j+4, 3*j+5} : Finset ℕ) := by simp
  have hi2 : 3*j+4 ∉ ({3*j+5} : Finset ℕ) := by simp
  rw [Finset.sum_insert hi1, Finset.sum_insert hi2,
      Finset.sum_singleton]
  have := hbal j hj; omega

/-- Assemblage de la fonction u a partir d'une suite de
    valeurs de grille x_j (delta d'etage = 9.10^{3(j+1)}.x_j) :
    chaque x_j se decompose en d1 + 11.d2 (grille) ou vaut 0,
    on pose D(3j+3) = -(d1+d2), D(3j+4) = d1, D(3j+5) = d2,
    et u = ubase + D. Alors u in [0,8], somme 4L+r0, et la
    fibre bouge de la somme des deltas d'etage. -/
theorem build_u (s r0 L : ℕ) (hs : 3 * s + 4 ≤ L) (hr0 : r0 ≤ 4)
    (x : ℕ → ℤ)
    (hx : ∀ j < s, (x j = 0) ∨ ∃ d1 d2 : ℤ,
      -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
      -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧ x j = d1 + 11 * d2) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ℤ) = (fibre (ubase s r0) L : ℤ) +
        ∑ j ∈ Finset.range s,
          9 * 10 ^ (3 * (j + 1)) * x j) := by
  classical
  -- decomposition de grille par choix, (0,0) si x j = 0
  have hdx : ∀ j < s, ∃ d1 d2 : ℤ,
      -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
      -4 ≤ d1 + d2 ∧ d1 + d2 ≤ 4 ∧ x j = d1 + 11 * d2 := by
    intro j hj
    rcases hx j hj with h0 | h
    · exact ⟨0, 0, by omega, by omega, by omega, by omega,
        by omega, by omega, by rw [h0]; ring⟩
    · exact h
  choose! d1 d2 hd using hdx
  -- delta sur les triplets : position e = 3 + (3j + r), r<3
  let D : ℕ → ℤ := fun e =>
    if 3 ≤ e ∧ e < 3 * s + 3 then
      (let j := (e - 3) / 3
       let r := (e - 3) % 3
       if r = 0 then -(d1 j + d2 j)
       else if r = 1 then d1 j else d2 j)
    else 0
  have hDt : ∀ j < s, D (3*j+3) = -(d1 j + d2 j) ∧
      D (3*j+4) = d1 j ∧ D (3*j+5) = d2 j := by
    intro j hj
    have hc1 : 3 ≤ 3*j+3 ∧ 3*j+3 < 3*s+3 := ⟨by omega, by omega⟩
    have hc2 : 3 ≤ 3*j+4 ∧ 3*j+4 < 3*s+3 := ⟨by omega, by omega⟩
    have hc3 : 3 ≤ 3*j+5 ∧ 3*j+5 < 3*s+3 := ⟨by omega, by omega⟩
    have e1 : (3*j+3) - 3 = 3*j := by omega
    have e2 : (3*j+4) - 3 = 3*j+1 := by omega
    have e3 : (3*j+5) - 3 = 3*j+2 := by omega
    have q1 : (3*j+3-3)/3 = j := by rw [e1]; omega
    have q2 : (3*j+4-3)/3 = j := by rw [e2]; omega
    have q3 : (3*j+5-3)/3 = j := by rw [e3]; omega
    have r1 : (3*j+3-3)%3 = 0 := by rw [e1]; omega
    have r2 : (3*j+4-3)%3 = 1 := by rw [e2]; omega
    have r3 : (3*j+5-3)%3 = 2 := by rw [e3]; omega
    simp only [D]
    rw [if_pos hc1, if_pos hc2, if_pos hc3]
    simp only [q1, q2, q3, r1, r2, r3]
    norm_num
  have hT : ∀ e, e ∉ (Finset.range s).biUnion
      (fun j => ({3*j+3, 3*j+4, 3*j+5} : Finset ℕ)) →
      D e = 0 := by
    intro e he
    simp only [D]
    by_cases hcond : 3 ≤ e ∧ e < 3 * s + 3
    · exfalso
      apply he
      rw [Finset.mem_biUnion]
      refine ⟨(e - 3) / 3, ?_, ?_⟩
      · rw [Finset.mem_range]
        have := hcond.2
        omega
      · have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        have hm : (e - 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
    · rw [if_neg hcond]
  have hbal : ∀ j < s,
      D (3*j+3) + D (3*j+4) + D (3*j+5) = 0 := by
    intro j hj
    obtain ⟨e1, e2, e3⟩ := hDt j hj
    rw [e1, e2, e3]; ring
  -- u = ubase + D (positif : ubase = 4 sur les triplets)
  have hnn : ∀ e, 0 ≤ (ubase s r0 e : ℤ) + D e := by
    intro e
    by_cases hc : 3 ≤ e ∧ e < 3 * s + 3
    · have hj : (e - 3) / 3 < s := by omega
      have hub : ubase s r0 e = 4 := by
        apply ubase_triple s r0 ((e-3)/3) e hj
        have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
      rw [hub]
      simp only [D]
      rw [if_pos hc]
      have hb := hd ((e-3)/3) hj
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb
      by_cases hr0' : (e-3) % 3 = 0
      · rw [if_pos hr0']; omega
      · by_cases hr1' : (e-3) % 3 = 1
        · rw [if_neg hr0', if_pos hr1']; omega
        · rw [if_neg hr0', if_neg hr1']; omega
    · simp only [D]; rw [if_neg hc]
      have := ubase_le s r0 hr0 e; omega
  have hle8 : ∀ e < L,
      (Int.toNat ((ubase s r0 e : ℤ) + D e)) ≤ 8 := by
    intro e _
    by_cases hc : 3 ≤ e ∧ e < 3 * s + 3
    · have hj : (e - 3) / 3 < s := by omega
      have hub : ubase s r0 e = 4 := by
        apply ubase_triple s r0 ((e-3)/3) e hj
        have h3 : e = 3 * ((e - 3) / 3) + 3 + (e - 3) % 3 := by
          have hdv := Nat.div_add_mod (e - 3) 3
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases (by omega : (e-3) % 3 = 0 ∨ (e-3) % 3 = 1 ∨
            (e-3) % 3 = 2) with hr | hr | hr
        · left; rw [hr] at h3; omega
        · right; left; rw [hr] at h3; omega
        · right; right; rw [hr] at h3; omega
      rw [hub]
      simp only [D]
      rw [if_pos hc]
      have hb := hd ((e-3)/3) hj
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hb
      rw [Int.toNat_le]
      by_cases hr0' : (e-3) % 3 = 0
      · rw [if_pos hr0']; omega
      · by_cases hr1' : (e-3) % 3 = 1
        · rw [if_neg hr0', if_pos hr1']; omega
        · rw [if_neg hr0', if_neg hr1']; omega
    · simp only [D]; rw [if_neg hc]
      rw [Int.toNat_le]
      have := ubase_le s r0 hr0 e; omega
  refine ⟨fun e => Int.toNat ((ubase s r0 e : ℤ) + D e),
    hle8, ?_, ?_⟩
  · -- somme : identique a ubase car Σ D = 0
    have hcast : ∀ e, ((Int.toNat
        ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ) =
        (ubase s r0 e : ℤ) + D e := fun e =>
      Int.toNat_of_nonneg (hnn e)
    have hsumD : ∑ e ∈ Finset.range L, D e = 0 :=
      sum_stages_zero D L s (by omega) hT hbal
    have hFE : ∀ (f : ℕ → ℕ) (n : ℕ),
        ((List.range n).map f).sum =
          ∑ e ∈ Finset.range n, f e := by
      intro f n; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, ih,
            Finset.sum_range_succ]
    rw [hFE, ← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ e ∈ Finset.range L,
          ((Int.toNat ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ)
        = ∑ e ∈ Finset.range L, ((ubase s r0 e : ℤ) + D e) :=
          Finset.sum_congr rfl fun e _ => hcast e
      _ = (∑ e ∈ Finset.range L, (ubase s r0 e : ℤ)) + 0 := by
          rw [Finset.sum_add_distrib, hsumD]
      _ = ((4 * L + r0 : ℕ) : ℤ) := by
          rw [add_zero, ← Nat.cast_sum]
          congr 1
          rw [← hFE]
          exact ubase_sum s r0 L hr0 (by omega)
  · -- fibre : fibre_stages_delta
    have hd' : ∀ e, ((Int.toNat
        ((ubase s r0 e : ℤ) + D e) : ℕ) : ℤ) =
        ubase s r0 e + D e := fun e =>
      Int.toNat_of_nonneg (hnn e)
    have hf := fibre_stages_delta (ubase s r0)
      (fun e => Int.toNat ((ubase s r0 e : ℤ) + D e)) D L s
      (by omega) hd' hT hbal
    rw [hf]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨e1, e2, e3⟩ := hDt j hj
    rw [e2, e3]
    have := hd j hj
    obtain ⟨-, -, -, -, -, -, hxeq⟩ := this
    rw [hxeq]

/-- g = gcd(9,m) est l'un de 1, 3, 9 (diviseur de 9 = 3^2). -/
theorem gcd9mem (m : ℕ) :
    Nat.gcd 9 m = 1 ∨ Nat.gcd 9 m = 3 ∨ Nat.gcd 9 m = 9 := by
  have h : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
  obtain ⟨k, hk, hke⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.gcd 9 m ∣ 3 ^ 2 from h)
  rw [hke]
  interval_cases k <;> simp

/-- `xres` = `emod` positif : `x % M ∈ [0, M)` donc `(x % M + M) % M = x % M`. -/
theorem xres_eq (M : Nat) (_hM : 0 < M) (x : Int) :
    xres M x = (x % (M : Int)).toNat := by
  unfold xres
  rw [Int.add_emod_right, Int.emod_emod]

/-- `xres` vu dans `ZMod M` coincide avec le cast `Int`. -/
theorem xres_cast (M : Nat) (hM : 0 < M) (x : Int) :
    ((xres M x : Nat) : ZMod M) = (x : ZMod M) := by
  have hnn : 0 ≤ x % (M : Int) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.ne_of_gt hM))
  rw [xres_eq M hM x]
  rw [← Int.cast_natCast (R := ZMod M), Int.toNat_of_nonneg hnn]
  rw [ZMod.intCast_eq_intCast_iff]
  exact Int.mod_modEq _ _

/-- Forme deployee de `stageRes` (elimination du `let`). -/
theorem stageRes_def (M i g : Nat) (xs : List Int) :
    stageRes M i g xs
      = (xs.map fun x =>
          ((((9 / g) * 10 ^ (3 * i)) % M) * xres M x) % M).eraseDups :=
  rfl

/-- `stageRes` vue dans `ZMod M` = le morceau non nul de `stageSet`. -/
theorem stageRes_image (M i g : Nat) (hM : 0 < M) (xs : List Int) :
    ((stageRes M i g xs).toFinset.image fun (s : ℕ) => (s : ZMod M))
      = xs.toFinset.image (fun (x : Int) =>
          ((9 / g : Nat) * 10 ^ (3 * i) : ZMod M) * (x : ZMod M)) := by
  rw [stageRes_def]
  ext z
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_eraseDups,
      List.mem_map]
  constructor
  · rintro ⟨a, ⟨x, hxs, rfl⟩, hza⟩
    refine ⟨x, hxs, ?_⟩
    rw [← hza, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod,
        xres_cast M hM x, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
  · rintro ⟨x, hxs, hcx⟩
    refine ⟨_, ⟨x, hxs, rfl⟩, ?_⟩
    rw [← hcx, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod,
        xres_cast M hM x, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]

/-- `setBits` = residus `< M` dont le bit est `1`. -/
theorem mem_setBits (M : Nat) (bits r : Nat) :
    r ∈ setBits M bits ↔ r < M ∧ bits.testBit r = true := by
  rw [setBits, List.mem_filter, List.mem_range]

/-- Poser le bit `k < M` : `setBits (a ||| 2^k) = setBits a ∪ {k}`. -/
theorem setBits_or_bit (M : Nat) (a k : Nat)
    (hk : k < M) :
    (setBits M (a ||| (1 <<< k))).toFinset
      = (setBits M a).toFinset ∪ {k} := by
  ext r
  rw [List.mem_toFinset, mem_setBits, Nat.testBit_or,
      Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow,
      Finset.mem_union, List.mem_toFinset, mem_setBits,
      Finset.mem_singleton, Bool.or_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, hb⟩
    rcases hb with hb | hkr
    · exact Or.inl ⟨hr, hb⟩
    · exact Or.inr hkr.symm
  · rintro (⟨hr, hb⟩ | rfl)
    · exact ⟨hr, Or.inl hb⟩
    · exact ⟨hk, Or.inr rfl⟩

/-- Le `foldl` OR-bit de `step` ajoute `{(r + s) % M | s ∈ l}` aux bits. -/
theorem inner_or (M : Nat) (hM : 0 < M) (r : Nat) :
    ∀ (l : List Nat) (a : Nat),
      (setBits M (l.foldl
          (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a)).toFinset
        = (setBits M a).toFinset
          ∪ l.toFinset.image (fun s => (r + s) % M) := by
  intro l a
  induction l generalizing a with
  | nil =>
    have h0 : (([] : List Nat).toFinset) = (∅ : Finset Nat) := rfl
    rw [List.foldl_nil, h0, Finset.image_empty, Finset.union_empty]
  | cons s l ih =>
    have hcons : (s :: l).toFinset = insert s l.toFinset := by
      ext x; simp
    rw [List.foldl_cons, ih (a ||| (1 <<< ((r + s) % M))),
        setBits_or_bit M a ((r + s) % M) (Nat.mod_lt _ hM),
        hcons, Finset.image_insert, Finset.insert_eq,
        Finset.union_assoc]

/-- `step` au niveau `Finset Nat` = somme de Minkowski `mod M`. -/
theorem step_aux (M : Nat) (hM : 0 < M) (stage : List Nat) :
    ∀ (l : List Nat) (a : Nat),
      (setBits M (l.foldl
          (fun a r => stage.foldl
            (fun a2 s => a2 ||| (1 <<< ((r + s) % M))) a) a)).toFinset
        = (setBits M a).toFinset ∪
          Finset.image₂ (fun r s => (r + s) % M) l.toFinset
            stage.toFinset := by
  intro l a
  induction l generalizing a with
  | nil =>
    have h0 : (([] : List Nat).toFinset) = (∅ : Finset Nat) := rfl
    rw [List.foldl_nil, h0, Finset.image₂_empty_left,
        Finset.union_empty]
  | cons r l ih =>
    have hcons : (r :: l).toFinset = insert r l.toFinset := by
      ext x; simp
    rw [List.foldl_cons,
        ih (stage.foldl (fun a2 s => a2 ||| (1 <<< ((r+s)%M))) a),
        inner_or M hM r stage a, hcons, Finset.image₂_insert_left,
        Finset.union_assoc]

/-- Version `step` de `step_aux`. -/
theorem step_bits (M : Nat) (hM : 0 < M) (acc : Nat)
    (stage : List Nat) :
    (setBits M (step M acc stage)).toFinset
      = (setBits M acc).toFinset ∪
        Finset.image₂ (fun r s => (r + s) % M) (setBits M acc).toFinset
          stage.toFinset := by
  exact step_aux M hM stage (setBits M acc) acc

/-- `image₂ ((r+s) % M)` puis `Nat.cast` = somme pointwise des images. -/
theorem image₂_cast (M : Nat) (A B : Finset Nat) :
    (Finset.image₂ (fun r s => (r + s) % M) A B).image
        (fun (r : ℕ) => (r : ZMod M))
      = (A.image fun (r : ℕ) => (r : ZMod M))
        + (B.image fun (s : ℕ) => (s : ZMod M)) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_image₂, Finset.mem_add]
  constructor
  · rintro ⟨p, ⟨a, ha, b, hb, rfl⟩, hza⟩
    refine ⟨(a : ZMod M), ⟨a, ha, rfl⟩, (b : ZMod M), ⟨b, hb, rfl⟩,
      ?_⟩
    rw [← hza, ZMod.natCast_mod, Nat.cast_add]
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, huv⟩
    refine ⟨(a + b) % M, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    rw [← huv, ZMod.natCast_mod, Nat.cast_add]

/-- `step` = somme de Minkowski `ZMod` avec `stage ∪ {0}`. -/
theorem step_image (M : Nat) (hM : 0 < M) (acc : Nat)
    (stage : List Nat) :
    ((setBits M (step M acc stage)).toFinset.image
        fun (r : ℕ) => (r : ZMod M))
      = ((setBits M acc).toFinset.image fun (r : ℕ) => (r : ZMod M))
        + ({0} ∪ stage.toFinset.image fun (s : ℕ) => (s : ZMod M)) := by
  rw [step_bits M hM acc stage, Finset.image_union,
      image₂_cast M, Finset.add_union, Finset.singleton_zero,
      add_zero]

/-- Un etage de plus dans `coverBits` = `step` avec `stageRes (j+1)`. -/
theorem coverBits_succ (M g : Nat) (xs : List Int) (j : Nat) :
    coverBits M g xs (j + 1)
      = step M (coverBits M g xs j) (stageRes M (j + 1) g xs) := by
  unfold coverBits
  rw [List.range_succ, List.foldl_append]
  simp

/-- `coverBits jmax` = bits de la somme de Minkowski des `jmax` etages. -/
theorem coverBits_image (M g : Nat) (hM : 0 < M) (xs : List Int) :
    ∀ jmax : Nat,
      ((setBits M (coverBits M g xs jmax)).toFinset.image
          fun (r : ℕ) => (r : ZMod M))
        = ∑ j ∈ Finset.range jmax, stageSet M (j+1) g xs := by
  intro jmax
  induction jmax with
  | zero =>
    have h0 : coverBits M g xs 0 = 1 := rfl
    have h1 : (setBits M 1).toFinset = {0} := by
      ext r
      rw [List.mem_toFinset, mem_setBits, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hb⟩
        exact Nat.testBit_one_eq_true_iff_self_eq_zero.mp hb
      · intro hr
        rw [hr]
        exact ⟨hM, Nat.testBit_one_eq_true_iff_self_eq_zero.mpr rfl⟩
    rw [h0, h1, Finset.image_singleton, Nat.cast_zero,
        Finset.range_zero, Finset.sum_empty, Finset.singleton_zero]
  | succ jmax ih =>
    rw [coverBits_succ, step_image M hM,
        stageRes_image M (jmax+1) g hM xs, ih]
    exact (Finset.sum_range_succ
      (fun j => stageSet M (j+1) g xs) jmax).symm

/-- PONT : `checkCoverB M g xs k = true` ⟹ la somme de Minkowski des
    `k` etages couvre `ZMod M` entier (forme `card = M`). -/
theorem coverB_to_finset (M g : Nat) [NeZero M] (xs : List Int) (k : Nat)
    (h : checkCoverB M g xs k = true) :
    ((Finset.range k).sum
      (fun j => stageSet M (j+1) g xs) : Finset (ZMod M)).card = M := by
  have hM : 0 < M := NeZero.pos M
  unfold checkCoverB at h
  have hcov : coverBits M g xs k = (1 <<< M) - 1 := beq_iff_eq.mp h
  rw [Nat.shiftLeft_eq, one_mul] at hcov
  have hsb : (setBits M (2 ^ M - 1)).toFinset = Finset.range M := by
    ext r
    rw [List.mem_toFinset, mem_setBits, Finset.mem_range,
        Nat.testBit_two_pow_sub_one]
    simp
  have huniv : ((setBits M (coverBits M g xs k)).toFinset.image
      fun (r : ℕ) => (r : ZMod M)) = Finset.univ := by
    rw [hcov, hsb]
    apply Finset.eq_univ_of_forall
    intro z
    rw [Finset.mem_image]
    refine ⟨z.val, Finset.mem_range.mpr (ZMod.val_lt z), ?_⟩
    have hv : ((z.val : ZMod M)).val = z.val :=
      ZMod.val_cast_of_lt (ZMod.val_lt z)
    exact ZMod.val_injective M hv
  have hsum := coverBits_image M g hM xs k
  rw [hsum] at huniv
  rw [huniv, Finset.card_univ, ZMod.card]

set_option maxRecDepth 40000 in
/-- Pour les trois moduls du coin (11, 19, 23) : 2 etages de
    Xsmooth235 couvrent ZMod m entier (g = 1 dans ces cas). -/
theorem stage_cover_2 (M g : ℕ) [NeZero M] (xs : List ℤ)
    (hM : M = 11 ∨ M = 19 ∨ M = 23) (hg : g = 1)
    (hxs : xs = Xsmooth235) :
    ∑ j ∈ Finset.range 2, stageSet M (j + 1) g xs =
      Finset.univ := by
  subst hg; subst hxs
  rcases hM with rfl | rfl | rfl <;>
    apply Finset.eq_univ_of_card <;>
    rw [ZMod.card] <;>
    decide

/-- Extraction du certificat : couverture en k <= m/27+1 etages
    pour M <= 184 hors coin. -/
theorem stage_cover_small' (m : ℕ) (hm : Nat.Coprime m 10)
    (hM : m / Nat.gcd 9 m ≤ 184)
    (hbad : ¬(m = 11 ∨ m = 19 ∨ m = 23)) :
    ∃ k ≤ m / 27 + 1,
      (∑ j ∈ Finset.range k,
        stageSet (m / Nat.gcd 9 m) (j + 1) (Nat.gcd 9 m)
          (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25)).card =
        m / Nat.gcd 9 m := by
  have hgpos : 0 < Nat.gcd 9 m :=
    Nat.gcd_pos_of_pos_left m (by norm_num)
  have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
  have hgl9 : Nat.gcd 9 m ≤ 9 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 9 m)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact h
  have hgl : Nat.gcd 9 m ≤ m := Nat.le_of_dvd hmpos hgm
  have hMpos : 0 < m / Nat.gcd 9 m := Nat.div_pos hgl hgpos
  haveI : NeZero (m / Nat.gcd 9 m) := ⟨Nat.ne_of_gt hMpos⟩
  have hm1656 : m ≤ 1656 := by
    calc m = m / Nat.gcd 9 m * Nat.gcd 9 m :=
          (Nat.div_mul_cancel hgm).symm
      _ ≤ 184 * 9 := Nat.mul_le_mul hM hgl9
      _ = 1656 := by norm_num
  have hmem : m ∈ List.range' 1 1656 :=
    List.mem_range'.mpr ⟨m - 1, by omega, by omega⟩
  have hall := List.all_eq_true.mp stage_cover_small_aux' m hmem
  have hgcop : Nat.gcd m 10 = 1 := hm
  have hcopb : (Nat.gcd m 10 == 1) = true :=
    beq_iff_eq.mpr hgcop
  have hd11 : decide (m = 11) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inl h))
  have hd19 : decide (m = 19) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inr (Or.inl h)))
  have hd23 : decide (m = 23) = false :=
    decide_eq_false_iff_not.mpr (fun h => hbad (Or.inr (Or.inr h)))
  have hdM : decide (m / Nat.gcd 9 m ≤ 184) = true :=
    decide_eq_true_iff.mpr hM
  simp only [hcopb, Bool.not_true, hd11, hd19, hd23, hdM,
    Bool.false_or, Bool.or_self, Bool.or_false] at hall
  obtain ⟨k, hkmem, hk⟩ := List.any_eq_true.mp hall
  have hkl := List.mem_range.mp hkmem
  exact ⟨k, by omega,
    coverB_to_finset (m / Nat.gcd 9 m) (Nat.gcd 9 m)
      (if Nat.gcd 9 m = 1 then Xsmooth235 else Xsmooth25) k hk⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Certificat de la table witCorner : pour m in {11,19,23},
    L in {7,8,9}, r0 <= 4 et tout residu tv, une entree
    (m, L, tv, code) donne u_e = code/10^e%10 <= 8 de somme
    4L+r0 et de fibre congru a tv. -/
theorem witCorner_all :
    (([11, 19, 23] : List ℕ).all fun m =>
      (List.range' 7 3).all fun L =>
        (List.range 5).all fun r0 =>
          (List.range m).all fun tv =>
            witCorner.any fun e =>
              (e.1 == m) && (e.2.1 == L) && (e.2.2.1 == tv) &&
              (List.range L).all (fun i =>
                decide (e.2.2.2 / 10 ^ i % 10 ≤ 8)) &&
              (((List.range L).map fun i =>
                e.2.2.2 / 10 ^ i % 10).sum == 4 * L + r0) &&
              (fibre (fun i => e.2.2.2 / 10 ^ i % 10) L % m == tv)
            ) = true := by
  decide

/-- Extraction d'un temoin de la table pour le coin. -/
theorem corner_witness (m : ℕ) [NeZero m] (t : ZMod m)
    (L r0 : ℕ) (hL7 : 7 ≤ L) (hL9 : L ≤ 9) (hr0 : r0 ≤ 4)
    (hbad : m = 11 ∨ m = 19 ∨ m = 23) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ZMod m) = t) := by
  have hall := List.all_eq_true.mp witCorner_all
  have hm' : m ∈ ([11, 19, 23] : List ℕ) := by
    rcases hbad with rfl | rfl | rfl <;> decide
  have h1 := hall m hm'
  have hL' : L ∈ List.range' 7 3 := by
    apply List.mem_range'.mpr
    exact ⟨L - 7, by omega, by omega⟩
  have h2 := List.all_eq_true.mp h1 L hL'
  have hr0' : r0 ∈ List.range 5 :=
    List.mem_range.mpr (by omega)
  have h3 := List.all_eq_true.mp h2 r0 hr0'
  have htv : t.val ∈ List.range m :=
    List.mem_range.mpr (ZMod.val_lt t)
  have h4 := List.all_eq_true.mp h3 t.val htv
  obtain ⟨e, _he, hbool⟩ := List.any_eq_true.mp h4
  obtain ⟨hbool, hfib⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hQ⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hall8⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨hbool, hptv⟩ := (Bool.and_eq_true _ _).mp hbool
  obtain ⟨_hpm, _hpL⟩ := (Bool.and_eq_true _ _).mp hbool
  refine ⟨fun i => e.2.2.2 / 10 ^ i % 10, fun i hi => ?_, ?_, ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp hall8 i
      (List.mem_range.mpr hi))
  · exact beq_iff_eq.mp hQ
  · have hf := beq_iff_eq.mp hfib
    have hceq : ((fibre (fun i => e.2.2.2 / 10 ^ i % 10) L : ℕ) :
        ZMod m) = (t.val : ZMod m) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      rw [Nat.mod_eq_of_lt (ZMod.val_lt t)]
      exact hf
    rw [hceq, ZMod.natCast_rightInverse]

/-- La fibre de la base ubase vaut 5L+r0 modulo g | 9 :
    chaque (1+u_e).10^e vaut (1+u_e) mod g car 10 ≡ 1 (mod g). -/
theorem fibre_ubase_mod (s r0 L g : ℕ) (hr0 : r0 ≤ 4)
    (hL : 3 * s + 4 ≤ L) (hg : g ∣ 9) [NeZero g] :
    ((fibre (ubase s r0) L : ℕ) : ZMod g) =
      ((5 * L + r0 : ℕ) : ZMod g) := by
  have h9 : (9 : ZMod g) = 0 := by
    simpa using (CharP.cast_eq_zero_iff (ZMod g) g 9).mpr hg
  have h10 : (10 : ZMod g) = 1 := by
    have e : (10 : ZMod g) = 9 + 1 := by norm_num
    rw [e, h9, zero_add]
  have hsum : ((List.range L).map (ubase s r0)).sum =
      4 * L + r0 := ubase_sum s r0 L hr0 hL
  have hsumm : ∀ e ∈ Finset.range L,
      (((1 + ubase s r0 e) * 10 ^ e : ℕ) : ZMod g) =
        1 + (ubase s r0 e : ZMod g) := by
    intro e _
    push_cast
    rw [h10, one_pow, mul_one]
  have hFE : ((List.range L).map (ubase s r0)).sum =
      ∑ e ∈ Finset.range L, ubase s r0 e := by
    clear hL hsum hsumm
    induction L with
    | zero => simp
    | succ n ih =>
      rw [List.sum_range_succ, ih, Finset.sum_range_succ]
  rw [fibre_val, Nat.cast_sum, Finset.sum_congr rfl hsumm]
  -- Σ (1 + u_e) = L + Σ u_e = 5L + r0 dans ZMod g
  rw [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one,
    ← Nat.cast_sum, ← hFE, hsum, ← Nat.cast_add]
  congr 1
  ring

theorem residue_reach (m : ℕ) (hm : Nat.Coprime m 10)
    (t : ZMod m) (L r0 : ℕ)
    (hL : 3 * (m / 27 + 1) + 4 ≤ L) (hr0 : r0 ≤ 4)
    (hcos : ∃ c : ℤ, t = ((5 * L + r0 : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 ∧
      ((fibre u L : ZMod m) = t) := by
  obtain ⟨c, hcos⟩ := hcos
  set g := Nat.gcd 9 m with hgdef
  set M := m / g with hMdef
  have hg9 : g = 1 ∨ g = 3 ∨ g = 9 := gcd9mem m
  have hg9d : g ∣ 9 := Nat.gcd_dvd_left 9 m
  have hgm : g ∣ m := Nat.gcd_dvd_right 9 m
  have hpos : 0 < g := Nat.gcd_pos_of_pos_left m (by norm_num)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact h
  have hMg : m = M * g := (Nat.div_mul_cancel hgm).symm
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hMg; omega
    · exact h
  haveI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  haveI : NeZero g := ⟨Nat.ne_of_gt hpos⟩
  have hMd : M ∣ m := ⟨g, hMg⟩
  have hcopM : Nat.Coprime M 10 :=
    Nat.Coprime.coprime_dvd_left hMd hm
  -- g ∈ {1,3} → 3 ∤ M
  have h3M : g = 1 ∨ g = 3 → ¬ (3 ∣ M) := by
    intro hgc h3M'
    rcases hgc with hg1 | hg3'
    · have h3m : 3 ∣ m := h3M'.trans hMd
      have h3g : 3 ∣ g := Nat.dvd_gcd (by norm_num) h3m
      rw [hg1] at h3g; norm_num at h3g
    · obtain ⟨k', hk'⟩ := h3M'
      have h9m : 9 ∣ m := ⟨k', by rw [hMg, hg3', hk']; ring⟩
      have h9g : 9 ∣ g := Nat.dvd_gcd (dvd_refl 9) h9m
      rw [hg3'] at h9g; norm_num at h9g
  -- jeu d'unites selon g
  set xs := if g = 1 then Xsmooth235 else Xsmooth25 with hxsdef
  have hxsu : ∀ x ∈ xs, IsUnit (x : ZMod M) := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      have h3c : Nat.Coprime M 3 := Nat.coprime_comm.mp
        (Nat.prime_three.coprime_iff_not_dvd.mpr (h3M (Or.inl h)))
      exact xunit235 M (hcopM.mul_right h3c) x hx
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      exact xunit25 M hcopM x hx
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      exact xunit25 M hcopM x hx
  have hnd : xs.Nodup := by
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef]; decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
  have hxb : ∀ x ∈ xs, |x| ≤ 92 := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
  have hx0 : ∀ x ∈ xs, x ≠ 0 := by
    intro x hx
    rcases hg9 with h | h | h
    · rw [if_pos h] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
    · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hx
      fin_cases hx <;> decide
  have hsq : M ≤ (m / 27 + 1) * xs.length + 1 := by
    rcases hg9 with h | h | h
    · have hlen : xs.length = 28 := by
        rw [if_pos h] at hxsdef; rw [hxsdef]; decide
      rw [hlen, hMdef, h, Nat.div_one]; omega
    · have hlen : xs.length = 16 := by
        rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
      rw [hlen, hMdef, h]; omega
    · have hlen : xs.length = 16 := by
        rw [if_neg (by omega)] at hxsdef; rw [hxsdef]; decide
      rw [hlen, hMdef, h]; omega
  have hunit : IsUnit ((9 / g : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (scalar_unit m)
  have h10u : IsUnit ((10 : ℕ) : ZMod M) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_comm.mp hcopM)
  have htail : ∀ s : ℕ, 3 * s + 4 ≤ L →
      ∑ j ∈ Finset.range s, stageSet M (j + 1) g xs = Finset.univ →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
        ((List.range L).map u).sum = 4 * L + r0 ∧
        ((fibre u L : ZMod m) = t) := by
    intro s hs4' hkcov
    -- fibre ubase ≡ 5L+r0 (mod g)
    have hfibg : ((fibre (ubase s r0) L : ℕ) : ZMod g) =
        ((5 * L + r0 : ℕ) : ZMod g) :=
      fibre_ubase_mod s r0 L g hr0 hs4' hg9d
    -- g | fibre ubase - (5L+r0) en entiers
    have hgdvd : (g : ℤ) ∣
        (fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ) := by
      have hZ : ((fibre (ubase s r0) L : ℤ) : ZMod g) =
          ((5 * L + r0 : ℤ) : ZMod g) := by
        exact_mod_cast hfibg
      rw [ZMod.intCast_eq_intCast_iff] at hZ
      exact Int.modEq_iff_dvd.mp hZ.symm
    set B' := ((fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ)) / g
      with hB'def
    have hgB : g * B' =
        (fibre (ubase s r0) L : ℤ) - (5 * L + r0 : ℤ) := by
      have h := Int.ediv_mul_cancel hgdvd
      rw [← hB'def] at h; rw [mul_comm] at h; exact h
    -- cible : c - B' dans ZMod M
    set ct := ((c - B' : ℤ) : ZMod M) with hctdef
    have hctu : ct ∈
        ∑ j ∈ Finset.range s, stageSet M (j+1) g xs := by
      rw [hkcov]; exact Finset.mem_univ _
    obtain ⟨f, hf, hfsum⟩ := (mem_sum_range
      (fun j => stageSet M (j+1) g xs) ct s).mp hctu
    -- valeur de grille x_j par etage
    have hxj : ∀ j : ℕ, ∃ x : ℤ, (x = 0 ∨ x ∈ xs) ∧
        (j < s → f j = ((9/g : ℕ) * 10^(3*(j+1)) : ZMod M) *
          (x : ZMod M)) := by
      intro j
      by_cases hj : j < s
      · have hmem := hf j hj
        rw [stageSet, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image] at hmem
        rcases hmem with h0 | ⟨x, hxs, hfx⟩
        · exact ⟨0, Or.inl rfl, fun _ => by rw [h0]; simp⟩
        · exact ⟨x, Or.inr (List.mem_toFinset.mp hxs), fun _ => hfx.symm⟩
      · exact ⟨0, Or.inl rfl, fun h => absurd h hj⟩
    choose xj hxj using hxj
    have hxg : ∀ j < s, (xj j = 0) ∨ ∃ d1 d2 : ℤ,
        -4 ≤ d1 ∧ d1 ≤ 4 ∧ -4 ≤ d2 ∧ d2 ≤ 4 ∧
        -4 ≤ d1+d2 ∧ d1+d2 ≤ 4 ∧ xj j = d1 + 11 * d2 := by
      intro j hj
      rcases (hxj j).1 with h0 | hxs
      · exact Or.inl h0
      · right
        have hxg' : xj j ∈ Xgrid := by
          rcases hg9 with h | h | h
          · rw [if_pos h] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth235_sub _ hxs
          · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth25_sub _ hxs
          · rw [if_neg (by omega)] at hxsdef; rw [hxsdef] at hxs
            exact Xsmooth25_sub _ hxs
        obtain ⟨d1, d2, ha, hb, hc2, hd2, he, hf2, heq, -⟩ :=
          (Xgrid_mem_iff _).mp hxg'
        exact ⟨d1, d2, ha, hb, hc2, hd2, he, hf2, heq⟩
    obtain ⟨u, hu8, hsum, hfib⟩ :=
      build_u s r0 L hs4' hr0 xj hxg
    -- S = Σ (9/g).10^{3i}.x_j ; (S : ZMod M) = ct
    set S := ∑ j ∈ Finset.range s,
      ((9/g : ℕ) : ℤ) * 10^(3*(j+1)) * xj j with hSdef
    have hSM : (S : ZMod M) = ct := by
      rw [hfsum, hSdef]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast, Int.cast_ofNat, Nat.cast_pow,
        Nat.cast_ofNat]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [(hxj j).2 hj] <;> ring_nf
    -- g*S ≡ g*(c-B') (mod m)
    have hgm2 : (g : ℤ) * S ≡ (g : ℤ) * (c - B')
        [ZMOD (m : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← mul_sub]
      have hmod : S ≡ (c - B') [ZMOD (M : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff ..).mp hSM
      have hdvd := mul_dvd_mul_left (g : ℤ)
        (Int.modEq_iff_dvd.mp hmod)
      have hgi : (g : ℤ) * (M : ℤ) = (m : ℤ) := by
        rw [mul_comm, ← Int.natCast_mul, ← hMg]
      rwa [hgi] at hdvd
    -- fibre u ≡ (5L+r0) + g*c (mod m)
    have hfinal : (fibre u L : ℤ) ≡
        ((5 * L + r0 : ℕ) : ℤ) + (g : ℤ) * c
        [ZMOD (m : ℤ)] := by
      have h9S : (∑ j ∈ Finset.range s,
          9 * 10 ^ (3*(j+1)) * xj j : ℤ) = g * S := by
        rw [hSdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have h99 : (9 : ℤ) =
            (g : ℤ) * ((9/g : ℕ) : ℤ) := by
          have h99' := Nat.div_mul_cancel hg9d
          rw [mul_comm] at h99'
          exact_mod_cast h99'.symm
        rw [h99]; ring
      rw [hfib, h9S]
      have hub : (fibre (ubase s r0) L : ℤ) =
          (5 * L + r0 : ℤ) + (g : ℤ) * B' := by
        have h := hgB; omega
      rw [hub]
      have h2 : (g:ℤ)*B' + (g:ℤ)*S ≡ (g:ℤ)*c
          [ZMOD (m:ℤ)] := by
        have e := hgm2.add_right ((g:ℤ)*B')
        have e2 : (g:ℤ)*B' + (g:ℤ)*S =
            (g:ℤ)*S + (g:ℤ)*B' := add_comm _ _
        have e3 : (g:ℤ)*c =
            (g:ℤ)*(c-B') + (g:ℤ)*B' := by ring
        rwa [e2, e3]
      have e := h2.add_left ((5 * L + r0 : ℕ) : ℤ)
      rwa [show (5 * L + r0 : ℤ) + (g:ℤ)*B' + (g:ℤ)*S =
          (5*L+r0:ℤ) + ((g:ℤ)*B' + (g:ℤ)*S) from by ring]
    refine ⟨u, hu8, hsum, ?_⟩
    have hcast : ((fibre u L : ℤ) : ZMod m) =
        ((((5 * L + r0 : ℕ) : ℤ) + (g : ℤ) * c : ℤ) :
          ZMod m) :=
      (ZMod.intCast_eq_intCast_iff ..).mpr hfinal
    push_cast at hcast
    rw [hcast, hcos]
    push_cast <;> ring
  -- aiguillage : coin {11,19,23} / M > 184 / machine M ≤ 184
  by_cases hbad : m = 11 ∨ m = 19 ∨ m = 23
  · by_cases hL10 : 10 ≤ L
    · rcases hbad with rfl | rfl | rfl <;>
        refine htail 2 (by omega) ?_
      all_goals
        have hg1 : g = 1 := by rw [hgdef]; decide
        rw [hg1, Nat.div_one] at hMdef
        have hxs1 : xs = Xsmooth235 := by
          rw [if_pos hg1] at hxsdef; exact hxsdef
        refine stage_cover_2 M g xs ?_ hg1 hxs1
        rw [hMdef]; decide
    · push_neg at hL10
      exact corner_witness m t L r0
        (by rcases hbad with rfl | rfl | rfl <;> omega)
        (by omega) hr0 hbad
  · by_cases hM184 : 184 < M
    · exact htail (m / 27 + 1) hL
        (stage_cover M g xs.length (m / 27 + 1) xs hM184 hunit
          h10u hxsu hnd hxb hx0 (le_refl _) hsq)
    · push_neg at hM184
      have hM' : m / Nat.gcd 9 m ≤ 184 := by
        rw [← hgdef, ← hMdef]; exact hM184
      obtain ⟨k, hks, hkc⟩ := stage_cover_small' m hm hM' hbad
      refine htail k (by omega) ?_
      apply Finset.eq_univ_of_card
      rw [ZMod.card]
      exact hkc

theorem coverage (m : ℕ) (hm : Nat.Coprime m 10) (t : ZMod m) :
    ∃ C : ℕ, C ≤ m / 9 + 7 ∧ ∀ L : ℕ, C ≤ L → ∀ r0 : ℕ, r0 ≤ 4 →
      (∃ c : ℤ, t = ((5 * L + r0 : ℕ) : ZMod m) +
          ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
        ((List.range L).map u).sum = 4 * L + r0 ∧
        ((fibre u L : ZMod m) = t) := by
  refine ⟨3 * (m / 27 + 1) + 4, by omega, ?_⟩
  intro L hL r0 hr0 hcos
  exact residue_reach m hm t L r0 hL hr0 hcos

/-- Decomposition n = R.m : on retire de n toute la 2-partie puis
    toute la 5-partie ; 10 non-divisant n force l'une des deux
    a etre 1, donc R = 2^d ou R = 5^d, et gcd(m,10) = 1. -/
theorem decomp_Rm (n : ℕ) (hn0 : n ≠ 0) (h10 : ¬ 10 ∣ n) :
    ∃ R m d : ℕ, n = R * m ∧ Nat.Coprime m 10 ∧ R ∣ 10 ^ d ∧
      Nat.Coprime R m ∧ (R = 2 ^ d ∨ R = 5 ^ d) := by
  set q1 := Nat.divMaxPow n 2 with hq1
  set a := padicValNat 2 n with ha
  have hq1n : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hq1n; exact hn0 hq1n.symm
  set m := Nat.divMaxPow q1 5 with hm
  set b := padicValNat 5 q1 with hb
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  -- a et b ne sont pas tous deux >= 1 (sinon 10 | n)
  have hab : a = 0 ∨ b = 0 := by
    rcases Nat.eq_zero_or_pos a with h | ha1
    · exact Or.inl h
    rcases Nat.eq_zero_or_pos b with h | hb1
    · exact Or.inr h
    exfalso; apply h10
    have h2an : 2 ^ a ∣ n := ⟨q1, by rw [← hq1n]; ring⟩
    have h2n : 2 ∣ n := dvd_trans (dvd_pow_self 2 ha1.ne') h2an
    have h5bn : 5 ^ b ∣ n := ⟨m * 2 ^ a, by rw [← hq1n, ← hmq]; ring⟩
    have h5n : 5 ∣ n := dvd_trans (dvd_pow_self 5 hb1.ne') h5bn
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num : Nat.Coprime 2 5) h2n h5n
    exact this
  have h2 : Nat.Coprime m 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
  have h5 : Nat.Coprime m 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
  refine ⟨2 ^ a * 5 ^ b, m, a + b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hq1n, ← hmq]; ring
  · have hc : Nat.Coprime m (2 * 5) := Nat.Coprime.mul_right h2 h5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  · have h10a : 2 ^ a ∣ 10 ^ a := pow_dvd_pow_of_dvd (by norm_num) a
    have h10b : 5 ^ b ∣ 10 ^ b := pow_dvd_pow_of_dvd (by norm_num) b
    have h2a5b : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_left a (Nat.Coprime.pow_right b
        (by norm_num : Nat.Coprime 2 5))
    have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd h2a5b
      (h10a.trans (pow_dvd_pow 10 (Nat.le_add_right a b)))
      (h10b.trans (pow_dvd_pow 10 (Nat.le_add_left b a)))
    exact hd
  · exact (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right a h2) (Nat.Coprime.pow_right b h5)).symm
  · rcases hab with h0 | h0
    · refine Or.inr ?_; simp [h0]
    · refine Or.inl ?_; simp [h0]

/-- log2 n <= n/16 + 4 pour n >= 64 (borne grossiere :
    n < 2^(n/16+5) car n < 16(n/16+1) <= 2^(n/16+5)). -/
theorem log2_le_div16 (n : ℕ) (hn : 64 ≤ n) :
    Nat.log 2 n ≤ n / 16 + 4 := by
  suffices h : Nat.log 2 n < n / 16 + 5 by omega
  apply Nat.log_lt_of_lt_pow (by omega : n ≠ 0)
  set j := n / 16 with hj
  have hmod := Nat.mod_add_div n 16
  have hltm := Nat.mod_lt n (by norm_num : 0 < 16)
  have h1 : n < 16 * (j + 1) := by omega
  have h3 : j + 1 ≤ 2 ^ (j + 1) := (j + 1).lt_two_pow_self.le
  calc n < 16 * (j + 1) := h1
    _ ≤ 16 * 2 ^ (j + 1) := Nat.mul_le_mul_left _ h3
    _ = 2 ^ (j + 5) := by
      have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
      rw [h16, ← pow_add]; congr 1; omega
    _ = 2 ^ (n / 16 + 5) := by rw [hj]

/-- d <= log2 n des que 2^d <= n (re-export pour lisibilite). -/
theorem le_log2_of_pow_le {d n : ℕ} (hn : n ≠ 0) (h : 2 ^ d ≤ n) :
    d ≤ Nat.log 2 n :=
  Nat.le_log_of_pow_le (by norm_num) h

/-- Somme d une constante sur List.range . -/
theorem sum_map_const (s l c : ℕ) :
    ((List.range' s l).map fun _ => c).sum = c * l := by
  induction l generalizing s with
  | zero => simp
  | succ k ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih]; ring

/-- Fibre explicite : u_0 = 4 + r0, autres = 4 - somme 4L + r0,
    tous <= 8 des que r0 <= 4 et L >= 1. -/
theorem fibre_u_exists (L : ℕ) (hL : 1 ≤ L) (r0 : ℕ) (hr0 : r0 ≤ 4) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = 4 * L + r0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  refine ⟨fun e => if e = 0 then 4 + r0 else 4, ?_, ?_⟩
  · intro e _
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp; omega
    · simp [Nat.ne_of_gt he]
  · rw [List.range_eq_range', List.range'_succ, List.map_cons, List.sum_cons]
    have hmap : (List.range' 1 l).map (fun e => if e = 0 then 4 + r0 else 4)
        = (List.range' 1 l).map fun _ => (4 : ℕ) := by
      apply List.map_congr_left
      intro e he
      have hne : e ≠ 0 := by
        obtain ⟨i, -, rfl⟩ := List.mem_range'.mp he; omega
      simp [hne]
    rw [hmap, sum_map_const]
    simp; ring

/-- Reduction : n divise la concatenation n|N <=> m'|c
    avec m' = n/gcd(n,10^d). -/
theorem concat_div_iff (n c L : ℕ) (hn : 1 ≤ n) (d : ℕ) :
    n ∣ (n * 10 ^ (L + d) + c * 10 ^ d + n) ↔
    (n / Nat.gcd n (10 ^ d)) ∣ c := by
  have hsplit : n ∣ (n * 10 ^ (L + d) + c * 10 ^ d + n) ↔
      n ∣ c * 10 ^ d := by
    have h1 : n ∣ n * 10 ^ (L + d) + n :=
      Nat.dvd_add (Nat.dvd_mul_right n _) (dvd_refl n)
    rw [show n * 10 ^ (L + d) + c * 10 ^ d + n =
        (n * 10 ^ (L + d) + n) + c * 10 ^ d from by omega]
    exact Nat.dvd_add_right h1
  rw [hsplit]
  set g := Nat.gcd n (10 ^ d) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left n (10 ^ d)
  obtain ⟨t, ht⟩ := Nat.gcd_dvd_right n (10 ^ d)
  rw [← hg] at hm' ht
  have hm'e : n / g = m' := Nat.div_eq_of_eq_mul_right hgpos hm'
  have hte : 10 ^ d / g = t := Nat.div_eq_of_eq_mul_right hgpos ht
  have hcop : Nat.Coprime m' t := by
    rw [← hm'e, ← hte]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  constructor
  · intro h
    rw [hm'e]
    have h2 : g * m' ∣ c * (g * t) := by
      rw [← hm', ← ht]; exact h
    rw [show c * (g * t) = g * (c * t) from by ring] at h2
    have h3 : m' ∣ c * t := Nat.dvd_of_mul_dvd_mul_left hgpos h2
    exact hcop.dvd_of_dvd_mul_right h3
  · rintro ⟨k, hk⟩
    use k * t
    rw [hk]
    calc (n / g) * k * 10 ^ d
        = (n / g) * g * (k * t) := by rw [ht]; ring
      _ = n * (k * t) := by
          rw [show (n / g) * g * (k * t) =
              n / Nat.gcd n (10 ^ d) * Nat.gcd n (10 ^ d) * (k * t)
              from by rw [hg]]
          rw [Nat.div_mul_cancel (Nat.gcd_dvd_left n (10 ^ d))]

/-- Somme de la concatenation :
    sigma(concat(n,c,n)) = 2*sigma(n) + sigma(c). -/
theorem concat_sigma (n c L : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (hd : d = (Nat.digits 10 n).length)
    (hc : c < 10 ^ L) :
    (Nat.digits 10 (n * 10 ^ (L + d) + c * 10 ^ d + n)).sum
      = 2 * (Nat.digits 10 n).sum + (Nat.digits 10 c).sum := by
  have hnn : 0 < n := by omega
  have hN : n * 10 ^ (L + d) + c * 10 ^ d + n =
      n + 10 ^ d * (c + n * 10 ^ L) := by
    rw [pow_add]; ring
  rw [hN]
  have hlow : Nat.digits 10 (n + 10 ^ d * (c + n * 10 ^ L)) =
      Nat.digits 10 n ++ Nat.digits 10 (c + n * 10 ^ L) := by
    rw [hd]
    exact (Nat.digits_append_digits (by norm_num : (0 : ℕ) < 10)
      (n := n) (m := c + n * 10 ^ L)).symm
  rw [hlow, List.sum_append]
  have hmid : (Nat.digits 10 (c + n * 10 ^ L)).sum =
      (Nat.digits 10 c).sum + (Nat.digits 10 n).sum := by
    have hle : (Nat.digits 10 c).length ≤ L :=
      (Nat.digits_length_le_iff (by norm_num) c).mpr hc
    have he : (Nat.digits 10 c).length +
        (L - (Nat.digits 10 c).length) = L := by omega
    have hz := Nat.digits_append_zeroes_append_digits (b := 10)
      (k := L - (Nat.digits 10 c).length) (m := n) (n := c)
      (by norm_num) hnn
    rw [he] at hz
    have hcomm : c + 10 ^ L * n = c + n * 10 ^ L := by ring
    rw [hcomm] at hz
    rw [← hz, List.sum_append, List.sum_append, List.sum_replicate]
    simp
  rw [hmid]; ring

/-- Liste de chiffres de N = concat(n,c,n) : forme
    dn ++ dc ++ dn (little-endian). -/
theorem concat_digits (n c : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (hd : d = (Nat.digits 10 n).length) :
    Nat.digits 10 (n * 10 ^ ((Nat.digits 10 c).length + d) +
        c * 10 ^ d + n) =
      Nat.digits 10 n ++ Nat.digits 10 c ++ Nat.digits 10 n := by
  have hN : n * 10 ^ ((Nat.digits 10 c).length + d) + c * 10 ^ d + n
      = n + 10 ^ d * (c + 10 ^ (Nat.digits 10 c).length * n) := by
    rw [pow_add]; ring
  rw [hN, hd]
  rw [← Nat.digits_append_digits (b := 10) (by norm_num)
      (n := n) (m := c + 10 ^ (Nat.digits 10 c).length * n)]
  rw [← Nat.digits_append_digits (b := 10) (by norm_num)
      (n := c) (m := n)]
  rw [← List.append_assoc]

/-- Existence a partir du temoin c : si m'|c et
    sigma(c) = n - 2*sigma(n) >= 0, alors N = concat(n,c,n)
    convient. -/
theorem exists_of_wit (n c : ℕ) (hn : 1 ≤ n)
    (hdiv : (n / Nat.gcd n (10 ^ (Nat.digits 10 n).length)) ∣ c)
    (hs : (Nat.digits 10 c).sum + 2 * (Nat.digits 10 n).sum = n) :
    ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).sum = n ∧
      Nat.digits 10 n <:+ Nat.digits 10 N ∧
      Nat.digits 10 n <+: Nat.digits 10 N := by
  set d := (Nat.digits 10 n).length
  set L := (Nat.digits 10 c).length
  set N := n * 10 ^ (L + d) + c * 10 ^ d + n
  have hd : d = (Nat.digits 10 n).length := rfl
  refine ⟨N, by positivity, ?_, ?_, ?_, ?_⟩
  · exact (concat_div_iff n c L hn d).mpr hdiv
  · rw [show N = n * 10 ^ (L + d) + c * 10 ^ d + n from rfl,
        concat_sigma n c L hn d hd
          (Nat.lt_base_pow_length_digits (by norm_num))]
    omega
  · rw [show N = n * 10 ^ (L + d) + c * 10 ^ d + n from rfl,
        concat_digits n c hn d hd]
    exact ⟨Nat.digits 10 n ++ Nat.digits 10 c, by simp⟩
  · rw [show N = n * 10 ^ (L + d) + c * 10 ^ d + n from rfl,
        concat_digits n c hn d hd]
    exact ⟨Nat.digits 10 c ++ Nat.digits 10 n, by simp⟩

/-- m' = n/gcd(n,10^d) n'est jamais divisible par 10 :
    sinon 10^{d+1} | n, or n < 10^d. -/
theorem mp_not10 (n : ℕ) (hn : 1 ≤ n) :
    ¬ 10 ∣ n / Nat.gcd n (10 ^ (Nat.digits 10 n).length) := by
  intro h10
  set d := (Nat.digits 10 n).length with hd
  set g := Nat.gcd n (10 ^ d) with hg
  set m' := n / g with hm'
  have hn0 : n ≠ 0 := by omega
  have hgpos : 0 < g := by
    rw [hg]; exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgm : n = g * m' := by
    rw [hm', mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n _)).symm
  have hm'0 : m' ≠ 0 := fun h => hn0 (by rw [hgm, h, mul_zero])
  have hvd : ∀ p : ℕ, p.Prime → p ∣ m' → p ∣ 10 →
      d + 1 ≤ padicValNat p n := by
    intro p hp hpd hp10
    haveI : Fact p.Prime := ⟨hp⟩
    have hcd : padicValNat p m' =
        padicValNat p n - padicValNat p g :=
      padicValNat.div_of_dvd (Nat.gcd_dvd_left n (10 ^ d))
    have hfg := Nat.factorization_gcd hn0
      (pow_ne_zero d (show (10 : ℕ) ≠ 0 by norm_num))
    have hcg : padicValNat p g =
        min (padicValNat p n) (padicValNat p (10 ^ d)) := by
      have happ := DFunLike.congr_fun hfg p
      rw [Finsupp.inf_apply] at happ
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
          Nat.factorization_def _ hp] at happ
      rw [hg]; exact happ
    have h10v : padicValNat p 10 = 1 := by
      have h1 : 1 ≤ padicValNat p 10 :=
        (padicValNat_dvd_iff_le_of_ne_one hp.ne_one
          (by norm_num)).mp (by simpa using hp10)
      have h2 : padicValNat p 10 < 2 := by
        by_contra h
        push_neg at h
        have hsq : p ^ 2 ∣ 10 :=
          (padicValNat_dvd_iff_le_of_ne_one hp.ne_one
            (by norm_num)).mpr h
        have hle : p ^ 2 ≤ 10 := Nat.le_of_dvd (by norm_num) hsq
        have hp3 : p ≤ 3 := by nlinarith
        interval_cases p <;> revert hsq hp <;> decide
      omega
    have hge1 : 1 ≤ padicValNat p m' :=
      (padicValNat_dvd_iff_le hm'0).mp (by simpa using hpd)
    have hvpd : padicValNat p (10 ^ d) = d := by
      rw [padicValNat.pow, h10v, mul_one]
    rw [hcd, hcg, hvpd] at hge1
    omega
  have h2m : 2 ∣ m' := (by norm_num : (2 : ℕ) ∣ 10).trans h10
  have h5m : 5 ∣ m' := (by norm_num : (5 : ℕ) ∣ 10).trans h10
  have h2n : 2 ^ (d + 1) ∣ n := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact (padicValNat_dvd_iff_le hn0).mpr
      (hvd 2 (by norm_num) h2m (by norm_num))
  have h5n : 5 ^ (d + 1) ∣ n := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact (padicValNat_dvd_iff_le hn0).mpr
      (hvd 5 (by norm_num) h5m (by norm_num))
  have h10n : 10 ^ (d + 1) ∣ n := by
    rw [show (10 : ℕ) = 2 * 5 from by norm_num, Nat.mul_pow]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _
        (by norm_num : Nat.Coprime 2 5))) h2n h5n
  have hlt : n < 10 ^ d :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have hle : 10 ^ (d + 1) ≤ n := Nat.le_of_dvd (by omega) h10n
  have hgt : (10 : ℕ) ^ d < 10 ^ (d + 1) := by
    rw [pow_succ]; nlinarith [Nat.one_le_pow d 10 (by norm_num)]
  omega

def wit739 : ℕ → ℕ
  | 10 => 8
  | 12 => 6
  | 13 => 104
  | 14 => 112
  | 15 => 3
  | 16 => 20
  | 18 => 0
  | 20 => 79
  | 21 => 168
  | 22 => 77
  | 23 => 184
  | 24 => 48
  | 25 => 29
  | 26 => 91
  | 27 => 27
  | 28 => 35
  | 29 => 232
  | 30 => 699
  | 31 => 2759
  | 32 => 688
  | 33 => 759
  | 34 => 578
  | 35 => 469
  | 36 => 99
  | 37 => 296
  | 38 => 475
  | 39 => 78
  | 40 => 6998
  | 41 => 18778
  | 42 => 4998
  | 43 => 4988
  | 44 => 5599
  | 45 => 999
  | 46 => 989
  | 47 => 799
  | 48 => 888
  | 49 => 2597
  | 50 => 49999
  | 51 => 68799
  | 52 => 58799
  | 53 => 29998
  | 54 => 19899
  | 55 => 53999
  | 56 => 9898
  | 57 => 17898
  | 58 => 6989
  | 59 => 8968
  | 60 => 399999
  | 61 => 598898
  | 62 => 579979
  | 63 => 199899
  | 64 => 299888
  | 65 => 179998
  | 66 => 339999
  | 67 => 169979
  | 68 => 79798
  | 69 => 66999
  | 70 => 3999989
  | 71 => 1999999
  | 72 => 1999998
  | 73 => 2999789
  | 74 => 3589999
  | 75 => 699999
  | 76 => 699998
  | 77 => 3299989
  | 78 => 599898
  | 79 => 779888
  | 80 => 39999988
  | 81 => 19899999
  | 82 => 28799999
  | 83 => 19799899
  | 84 => 8899989
  | 85 => 7898999
  | 86 => 7799899
  | 87 => 3999999
  | 88 => 12999998
  | 89 => 5988988
  | 90 => 99999999
  | 91 => 499679999
  | 92 => 89999989
  | 93 => 98999988
  | 94 => 89798999
  | 95 => 69889999
  | 96 => 69999888
  | 97 => 58998989
  | 98 => 47899999
  | 99 => 109899999
  | 100 => 89999999999
  | 101 => 89989999999
  | 102 => 79999999899
  | 103 => 79988999999
  | 104 => 59999899999
  | 105 => 49999899999
  | 106 => 48999998999
  | 107 => 39999997999
  | 108 => 19899999999
  | 109 => 19999899989
  | 110 => 889999999999
  | 111 => 888999999999
  | 112 => 799989999998
  | 113 => 698999899999
  | 114 => 499999998999
  | 115 => 399999989999
  | 116 => 389999999998
  | 117 => 297999999999
  | 118 => 198999899999
  | 119 => 99998999989
  | 120 => 6999999999999
  | 121 => 8799999998999
  | 122 => 6899999899999
  | 123 => 6897999999999
  | 124 => 4989899999999
  | 125 => 1999999999999
  | 126 => 999999999999
  | 127 => 1989899999999
  | 128 => 1999999999888
  | 129 => 889999899999
  | 130 => 69899999999999
  | 131 => 78989999998999
  | 132 => 66999999999999
  | 133 => 59989979999999
  | 134 => 48989989999999
  | 135 => 19899999999999
  | 136 => 9999999999989
  | 137 => 8999999899999
  | 138 => 7999999998999
  | 139 => 8988999998999
  | 140 => 599989999999999
  | 141 => 588999999999999
  | 142 => 499998899999999
  | 143 => 699697999999999
  | 144 => 199999999999998
  | 145 => 198989999999999
  | 146 => 98999998999999
  | 147 => 89997999999999
  | 148 => 185999999999999
  | 149 => 68999999899999
  | 150 => 3999999999999999
  | 151 => 3999998999999999
  | 152 => 3899999989999999
  | 153 => 1999999999899999
  | 154 => 4697999999999999
  | 155 => 1799999999999899
  | 156 => 897999999999999
  | 157 => 879999989999999
  | 158 => 879999989899999
  | 159 => 499999998999999
  | 160 => 49999999999999988
  | 161 => 58899999999899989
  | 162 => 19899999999999999
  | 163 => 19998998999999999
  | 164 => 28879999999999999
  | 165 => 42999999999999999
  | 166 => 7979999999999999
  | 167 => 7999988999998999
  | 168 => 4998999999999999
  | 169 => 5898999899999999
  | 170 => 298999999999999999
  | 171 => 199999999999899999
  | 172 => 198999999999999998
  | 173 => 99799999999999999
  | 174 => 88999999999899999
  | 175 => 68999999999999999
  | 176 => 239999999999999998
  | 177 => 59998999999989999
  | 178 => 48899999999999999
  | 179 => 49989998998999999
  | 180 => 999999999999999999
  | 181 => 1998899999999999999
  | 182 => 899899999999999999
  | 183 => 899999899999998999
  | 184 => 789999989999999999
  | 185 => 2479999999999999999
  | 186 => 598989999999999999
  | 187 => 2299989999999998999
  | 188 => 399989999998999999
  | 189 => 298998999999999999
  | 190 => 9999999989999999999
  | 191 => 9999999999998989999
  | 192 => 9999999999999999888
  | 193 => 7989999999999998999
  | 194 => 6999999999999998989
  | 195 => 4899999999999999999
  | 196 => 4999799999999999999
  | 197 => 3999999999899999899
  | 198 => 999999999999999999
  | 199 => 999999999999899999
  | 200 => 7999999999999999999999
  | 201 => 8989999999999999999899
  | 202 => 8987999999999999999999
  | 203 => 7898999999999899999999
  | 204 => 4999998999999999999999
  | 205 => 5798999999999999999999
  | 206 => 3998999999999998999999
  | 207 => 1999999998999999999999
  | 208 => 1899999999999999999998
  | 209 => 999998999999999899999
  | 210 => 79989999999999999999999
  | 211 => 79999999999999998998999
  | 212 => 69998998999999999999999
  | 213 => 49999999999999999999998
  | 214 => 49899999999999999989999
  | 215 => 38999999989999999999999
  | 216 => 19899999999999999999999
  | 217 => 19999999999999899899999
  | 218 => 9999899999999999999989
  | 219 => 9999987999999999999999
  | 220 => 779999999999999999999999
  | 221 => 699989999999899999999999
  | 222 => 777999999999999999999999
  | 223 => 589999998999999989999999
  | 224 => 498999999999999999999988
  | 225 => 99999999999999999999999
  | 226 => 199989999999999999999899
  | 227 => 99998999999999999998999
  | 228 => 79999999999989999999999
  | 229 => 79999898999999999999999
  | 230 => 5989999999999999999999999
  | 231 => 7698999999999999999999999
  | 232 => 3989999999999999999999999
  | 233 => 3999998999999999998999999
  | 234 => 999999999999999999999999
  | 235 => 999999999999999999989999
  | 236 => 998999999999999899999999
  | 237 => 899999979999999999999999
  | 238 => 799999898999999999999999
  | 239 => 899878999999999999999999
  | 240 => 49999999999999999999999998
  | 241 => 58999999999989999998999999
  | 242 => 56999999999999989999999999
  | 243 => 19999999999899999999999999
  | 244 => 19899999998999999999999999
  | 245 => 8999999999998999999999999
  | 246 => 18978999999999999999999999
  | 247 => 7999999899999989999999999
  | 248 => 5998999999999999999999999
  | 249 => 4999899999999999999999999
  | 250 => 299999999999999999999999999
  | 251 => 389999999999999999999989999
  | 252 => 189999999999999999999999999
  | 253 => 559898999999999999999999999
  | 254 => 99999989989999999999999999
  | 255 => 79999899999999999999999999
  | 256 => 99999999999999999999989888
  | 257 => 69989999989999999999999999
  | 258 => 59989998999999999999999999
  | 259 => 79994999999999999999999999
  | 260 => 2899999999999999999999999999
  | 261 => 1999999998999999999999999999
  | 262 => 999999999989999999999999999
  | 263 => 999999999999989999999989999
  | 264 => 3399999999999999999999999999
  | 265 => 788999999999999999999999999
  | 266 => 599989999999999999999999999
  | 267 => 598999999999999999998999999
  | 268 => 399999999999999999999899999
  | 269 => 398999999999999999998999999
  | 270 => 19899999999999999999999999999
  | 271 => 77786999999999999999999999999
  | 272 => 9999999999999989999999999998
  | 273 => 7999899999999999999999999999
  | 274 => 8999899799999999999999999999
  | 275 => 31999999999999999999999999999
  | 276 => 4999999999999999999899999999
  | 277 => 4989999999899999999999999999
  | 278 => 2999999999999989999999999999
  | 279 => 1999999999899999999999999999
  | 280 => 89999999999999999999999999999
  | 281 => 99998999999989999999999999999
  | 282 => 88999999999999989999999999999
  | 283 => 77999999999999999999999999999
  | 284 => 49999999999999999999999999999
  | 285 => 49999989999999999999999999999
  | 286 => 139997999999999999999999999999
  | 287 => 48899999999989999999999999999
  | 288 => 29999999999999999999999999988
  | 289 => 19999999998899999999999999999
  | 290 => 899999999999999999899999999999
  | 291 => 889899999999999999999999999999
  | 292 => 889989989999999999999999999999
  | 293 => 699999999997999999999999999999
  | 294 => 589999999999999999989999999999
  | 295 => 399999999999999999999999899999
  | 296 => 1369999999999999999999999999999
  | 297 => 1099999899999999999999999999999
  | 298 => 199998999999999999998999999999
  | 299 => 98999999999899999999999999999
  | 300 => 699999999999999999999999999999999
  | 301 => 799999989999999899999999999999999
  | 302 => 699999999999999899999999999999998
  | 303 => 796899999999999999999999999999999
  | 304 => 499999999999999899999999999999998
  | 305 => 398999999999999999999999998999999
  | 306 => 99999999999999999999999999999999
  | 307 => 189999999999999999999999899999999
  | 308 => 99998899999999999999999999999999
  | 309 => 88999999999999999999998999999999
  | 310 => 7899999999999899999999999999999999
  | 311 => 6999999999989999999999989999999999
  | 312 => 5889999999999999999999999999999999
  | 313 => 4999899999999999999999989999999999
  | 314 => 3999999999999999989999989999999999
  | 315 => 1999989999999999999999999999999999
  | 316 => 999989999999999999999999999999999
  | 317 => 899999999999999999998999999999999
  | 318 => 899999899899999999999999999999999
  | 319 => 889899999999999999999999989999999
  | 320 => 79999999999999999999999999999999888
  | 321 => 58999999999999999999989999999999999
  | 322 => 48999998999999999999999999999999999
  | 323 => 39899999999999999999999998999999999
  | 324 => 19899999999999999999999999999999999
  | 325 => 19799999999999999999999999999999999
  | 326 => 9998999999999999998999999999999999
  | 327 => 8999989999999999999998999999999999
  | 328 => 8897999999999999999999999999999999
  | 329 => 6979999999999999999999999999999999
  | 330 => 669999999999999999999999999999999999
  | 331 => 489999999999999999999998999999999999
  | 332 => 299999999999999999999999999989999999
  | 333 => 666999999999999999999999999999999999
  | 334 => 189999998999999999999999999999999999
  | 335 => 89999999999999999999998999999999999
  | 336 => 88999999999999999999999999999999998
  | 337 => 79999999999999999999899999999989999
  | 338 => 69989999999999999999999999989999999
  | 339 => 49999999999999998999999999999999999
  | 340 => 3989999999999999999999999999999999999
  | 341 => 6797999999999999999999989999999999999
  | 342 => 999999999999999999999999999999999999
  | 343 => 1998999999999999999999999999999999899
  | 344 => 999989998999999999999999999999999999
  | 345 => 799999999999999999989999999999999999
  | 346 => 799989999999989999999999999999999999
  | 347 => 699999899999999999998999999999999999
  | 348 => 499999999999999999999989999999999999
  | 349 => 499999998999899999999999999999999999
  | 350 => 28999999999999999999999999999999999999
  | 351 => 47998899999999999999999999999999999999
  | 352 => 47999999999999999999999999999999999996
  | 353 => 9999989899999999999999999999999999999
  | 354 => 8989999999999999999999999999999999989
  | 355 => 7989999999999999999989999999999999999
  | 356 => 5999999999999999999999999999999999899
  | 357 => 4999999999999999999999999989999999999
  | 358 => 4999999999899999998999999999999999999
  | 359 => 3899999999899999999999999999999999999
  | 360 => 99999999999999999999999999999999999999
  | 361 => 199999999998999999999999999999999999989
  | 362 => 89999999999999999999999999998999999999
  | 363 => 439999999899999999999999999999999999999
  | 364 => 89988899999999999999999999999999999999
  | 365 => 69999799999999999999999999999999999999
  | 366 => 59989899999999999999999999999999999999
  | 367 => 49999899999999999999999989999999999999
  | 368 => 39999999999899999999999999999999999998
  | 369 => 29988999999999999999999999999999999999
  | 370 => 3959999999999999999999999999999999999999
  | 371 => 1889999999999999999999998999999999999999
  | 372 => 799989999999999999999999999999999999999
  | 373 => 888999999989999999999999999999999999999
  | 374 => 2498999999999998999999999999999999999999
  | 375 => 399999999999999999999999999999999999999
  | 376 => 399999999999999999999999999999899999999
  | 377 => 489999999999999998999999899999999999999
  | 378 => 189999999999999999999999999999999999999
  | 379 => 199999899999999999999999999999989999999
  | 380 => 7999999999999999999999999999999999999999
  | 381 => 8899999999999999999999999998999999999999
  | 382 => 7999999899999999999999989999999999999999
  | 383 => 6999999999999989999999989999999999999999
  | 384 => 6999999999999999999999999999999999999888
  | 385 => 21999899999999999999999999999999999999999
  | 386 => 3999999899999999999999999999999999999998
  | 387 => 2989999989999999999999999999999999999999
  | 388 => 999999999999999999999999999999989999999
  | 389 => 989999999999999999999999999999989999999
  | 390 => 79989999999999999999999999999999999999999
  | 391 => 79999999999899999999999999999999999998999
  | 392 => 59999999999999999999999999999999999999899
  | 393 => 59989999999899999999999999999999999999999
  | 394 => 48999999999999999999999999999999899999999
  | 395 => 38998999999999999999999999999999999999999
  | 396 => 9999999999999999999999999999999999999999
  | 397 => 18999999999999999999999999999999999999989
  | 398 => 9999999999989999998999999999999999999999
  | 399 => 9979989999999999999999999999999999999999
  | 400 => 69999999999999999999999999999999999999999998
  | 401 => 69899999999899999999999999999999999999999999
  | 402 => 49999999999899999999999999999999999999999999
  | 403 => 49999999999999999998999999999899999999999999
  | 404 => 59599999999999999999999999999999999999999999
  | 405 => 19899999999999999999999999999999999999999999
  | 406 => 19999999999998999999999999999999999999989999
  | 407 => 29896999999999999999999999999999999999999999
  | 408 => 7999999989999999999999999999999999999999999
  | 409 => 7999999999999999999999999999999999989999998
  | 410 => 589999999999999999999999999999999999999999999
  | 411 => 699979989999999999999999999999999999999999999
  | 412 => 489999999999899999999999999999999999999999999
  | 413 => 399999999999999989999999989999999999999999999
  | 414 => 99999999999999999999999999999999999999999999
  | 415 => 99999999999999999899999999999999999999999999
  | 416 => 289999999999999999999999999999999999999999996
  | 417 => 89899999999999999999999999999999999999899999
  | 418 => 79999998989999999999999999999999999999999999
  | 419 => 78999989999999999999999999999899999999999999
  | 420 => 4998999999999999999999999999999999999999999999
  | 421 => 4989999999999999999999999989999999999999999999
  | 422 => 3989999999999999999999999899999999999999999999
  | 423 => 1999999999999999999999999899999999999999999999
  | 424 => 1999999899899999999999999999999999999999999999
  | 425 => 899999999899999999999999999999999999999999999
  | 426 => 899998999999999999999999999998999999999999999
  | 427 => 889999999998999999998999999999999999999999999
  | 428 => 698999999999999899999999999999999999999999999
  | 429 => 799797999999999999999999999999999999999999999
  | 430 => 39999999899999999999999999999999999999999999999
  | 431 => 39999999998999999999999999999999998999999999999
  | 432 => 28999999999999999999999999999999999999999999998
  | 433 => 19989999999999999999899999999999999999999999999
  | 434 => 9999989999999999998999999999999999999999999999
  | 435 => 7999999999999999998999999999999999999999999999
  | 436 => 8898999999999999999999999998999999999999999999
  | 437 => 6999999999999999989999999999899999999999999999
  | 438 => 4999998999999999999999999999999999999999999999
  | 439 => 3999999999999999999999999999999999999999989999
  | 440 => 559999999999999999999999999999999999999999999999
  | 441 => 199999999999999999999999999999999899999999999999
  | 442 => 199979999999999999999999999999999999999999999999
  | 443 => 99999999999998999999999989999999999999999999999
  | 444 => 89799999999999999999999999999999999999999999999
  | 445 => 79989999999999999999998999999999999999999999999
  | 446 => 59999999999998999999999999999999999999999999999
  | 447 => 58998999999999999999999999999999999999999999999
  | 448 => 78999899999999999999999999999999999999999999888
  | 449 => 48999999899899999999999999999999999999999999999
  | 450 => 999999999999999999999999999999999999999999999999
  | 451 => 5799989897999999999999999999999999999999999999999
  | 452 => 999899999999999999999999999999999999999999999899
  | 453 => 799999999999999999999999999999999999999899999999
  | 454 => 699999999999999999999999999999899999999999999999
  | 455 => 798889999999999999999999999999999999999999999999
  | 456 => 499999998999999999999999999999999999999999999999
  | 457 => 399999999999999999999999989999999999999999999999
  | 458 => 398999999999999999999999999999999999999999989999
  | 459 => 199999999989999999999999999999999999999999999999
  | 460 => 8999999999999999999999999999999999999999999999999
  | 461 => 9999999999999999999999999989999999999999999999899
  | 462 => 36989799999999999999999999999999999999999999999999
  | 463 => 7999989999999999999999999999999999999998999999999
  | 464 => 6999999999989999999999999999999999999999999999998
  | 465 => 3999999999999999999999999999999999999999999999999
  | 466 => 4989989999999999999999999999999999999999999999999
  | 467 => 3999999998999999999999999999999999999989999999999
  | 468 => 999999999999999999999999999999999999999999999999
  | 469 => 1999999999999989999999999989999999999999999999999
  | 470 => 89999999999999999999999999999999999999899999999999
  | 471 => 89999899999998999999999999999999999999999999999999
  | 472 => 69999999999999999998999999999999999999999999999999
  | 473 => 329899999999999999999999999999999999999999999999999
  | 474 => 67999998999999999999999999999999999999999999999999
  | 475 => 29999999999999999999999999999999999999999999999999
  | 476 => 39899999999999998999999999999999999999999999999999
  | 477 => 28999999999899999999999999999999999999999999999999
  | 478 => 57897989999999999999999999999999999999999999999999
  | 479 => 9999999999999999799999999999999999999999999999999
  | 480 => 899999999999999999999999999999999999999999999999988
  | 481 => 3848999999999999999999999999999999999999999999999999
  | 482 => 699999999999999889999999999999999999999999999999999
  | 483 => 399999999999999999999999999999999999999999999999999
  | 484 => 1299999899999999999999999999999999999999999999999999
  | 485 => 289999999999999999999999999999999999999999999999999
  | 486 => 199999999999989999999999999999999999999999999999999
  | 487 => 199899999999999999999999999998999999999999999999999
  | 488 => 89999989999999999999999999999999999999999999999999
  | 489 => 89999899989999999999999999999999999999999999999999
  | 490 => 6999999999999999999999998999999999999999999999999999
  | 491 => 6999999999999999999999999999999999999899899999999999
  | 492 => 6987999999999999999999999999999999999999999999999999
  | 493 => 4989999999999999999998999999999999999999999999999999
  | 494 => 4998989999999999989999999999999999999999999999999999
  | 495 => 10989999999999999999999999999999999999999999999999999
  | 496 => 999999999999999999999999999999999999999999999999998
  | 497 => 1989999999989999999999999999989999999999999999999999
  | 498 => 899899999999999999999999999999999899999999999999999
  | 499 => 799999799999999999999999999999999999999999999999999
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Certificat : chaque temoin wit739 verifie m'|c et
    sigma(c) = n - 2*sigma(n) pour n in [10,499] hors
    exceptions. -/
theorem wit739_spec (n : ℕ) (hn10 : 10 ≤ n) (hn500 : n < 500)
    (h11 : n ≠ 11) (h17 : n ≠ 17) (h19 : n ≠ 19) :
    (n / Nat.gcd n (10 ^ (Nat.digits 10 n).length)) ∣ wit739 n ∧
      (Nat.digits 10 (wit739 n)).sum +
        2 * (Nat.digits 10 n).sum = n := by
  interval_cases n <;> first
    | exact absurd rfl h11 | exact absurd rfl h17
    | exact absurd rfl h19 | decide

/-- sigma(n) <= 9 * longueur. -/
theorem sigma10_le_9len (n : ℕ) :
    sigma10 n ≤ 9 * (Nat.digits 10 n).length := by
  rw [sigma10]
  by_cases hn : n = 0
  · simp [hn]
  · have h9 : ∀ d ∈ Nat.digits 10 n, d ≤ 9 :=
      fun d hd => Nat.le_of_lt_succ
        (Nat.digits_lt_base (by norm_num) hd)
    have hle : ∀ l : List ℕ, (∀ d ∈ l, d ≤ 9) →
        l.sum ≤ 9 * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        rw [List.sum_cons, List.length_cons]
        have ha := hl a (List.mem_cons_self)
        have hi := ih (fun d hd => hl d
          (List.mem_cons_of_mem a hd))
        omega
    exact hle _ h9

/-- log10 n <= n/125 pour n >= 500. -/
theorem log10_le_125 (n : ℕ) (hn : 500 ≤ n) :
    Nat.log 10 n ≤ n / 125 := by
  set k := Nat.log 10 n
  have hk : 10 ^ k ≤ n := Nat.pow_log_le_self 10 (by omega)
  have h125 : ∀ j : ℕ, 3 ≤ j → 125 * j ≤ 10 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      have h9 : 125 ≤ 9 * 10 ^ j := by
        have : (1000 : ℕ) ≤ 10 ^ j :=
          calc (1000 : ℕ) = 10 ^ 3 := by norm_num
            _ ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        omega
      calc 125 * (j + 1) = 125 * j + 125 := by ring
        _ ≤ 10 ^ j + 9 * 10 ^ j := by omega
        _ = 10 ^ (j + 1) := by ring
  by_cases hk3 : 3 ≤ k
  · have : 125 * k ≤ n := le_trans (h125 k hk3) hk
    rw [Nat.mul_comm] at this
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
  · have h2 : k ≤ 2 := by omega
    omega

/-- log5 n <= n/100 pour n >= 500. -/
theorem log5_le_100 (n : ℕ) (hn : 500 ≤ n) :
    Nat.log 5 n ≤ n / 100 := by
  set k := Nat.log 5 n
  have hk : 5 ^ k ≤ n := Nat.pow_log_le_self 5 (by omega)
  have h100 : ∀ j : ℕ, 4 ≤ j → 100 * j ≤ 5 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      have h4 : 100 ≤ 4 * 5 ^ j := by
        have : (625 : ℕ) ≤ 5 ^ j :=
          calc (625 : ℕ) = 5 ^ 4 := by norm_num
            _ ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) hj
        omega
      calc 100 * (j + 1) = 100 * j + 100 := by ring
        _ ≤ 5 ^ j + 4 * 5 ^ j := by omega
        _ = 5 ^ (j + 1) := by ring
  by_cases hk4 : 4 ≤ k
  · have : 100 * k ≤ n := le_trans (h100 k hk4) hk
    rw [Nat.mul_comm] at this
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
  · have : k ≤ 3 := by omega
    omega

/-- Etape de concatenation a somme libre : c = B + 10^d.F
    avec R.m | c (R | B, R | 10^d, residu fibre). -/
theorem middle_step (R m B d s : ℕ)
    (hRc : Nat.Coprime R m) (hR10 : R ∣ 10 ^ d) (hRB : R ∣ B)
    (hBl : (Nat.digits 10 B).length = d) (hB0 : B ≠ 0)
    (L : ℕ) (u : ℕ → ℕ) (hu : ∀ e < L, u e ≤ 8)
    (hres : (fibre u L : ZMod m) * (10 : ZMod m) ^ d +
        (B : ZMod m) = 0)
    (hsum : sigma10 B + sigma10 (fibre u L) = s) :
    ∃ c : ℕ, R * m ∣ c ∧ sigma10 c = s := by
  have hdiv : R * m ∣ B + 10 ^ d * fibre u L := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hRc
    · exact dvd_concat_base R B _ d hR10 hRB
    · have hz : ((B + 10 ^ d * fibre u L : ℕ) : ZMod m) = 0 := by
        push_cast
        linear_combination hres
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hz
  refine ⟨B + 10 ^ d * fibre u L, hdiv, ?_⟩
  rw [← hBl, sigma_concat B _ hB0]; exact hsum

/-- Variante de existence_Rm a somme cible s libre.
    Le coset est garanti par g | s (avec L+K = s - sigma B). -/
theorem middle_Rm (s R m : ℕ)
    (hRc : Nat.Coprime R m) (hm : Nat.Coprime m 10)
    (d : ℕ) (hR10 : R ∣ 10 ^ d)
    (B : ℕ) (hRB : R ∣ B) (hBl : (Nat.digits 10 B).length = d)
    (hB0 : B ≠ 0) (hsB : sigma10 B ≤ s)
    (hgs : Nat.gcd 9 m ∣ s)
    (L K : ℕ) (hLK : L + K = s - sigma10 B)
    (hm1 : 1 < m)
    (hcov : ∀ t : ZMod m, (∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) →
      ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = K ∧
        (fibre u L : ZMod m) = t) :
    ∃ c : ℕ, R * m ∣ c ∧ sigma10 c = s := by
  have hunit : IsUnit ((10 : ZMod m) ^ d) := by
    apply IsUnit.pow
    exact (ZMod.isUnit_iff_coprime 10 m).mpr
      (Nat.coprime_comm.mp hm)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  set t : ZMod m := -(B : ZMod m) * v with ht
  have htgt : t * (10 : ZMod m) ^ d + (B : ZMod m) = 0 := by
    rw [ht, mul_assoc]
    have hv' : (v : ZMod m) * (10 : ZMod m) ^ d = 1 := by
      rw [mul_comm]; exact hv
    rw [hv']; simp
  have hcosB : ∃ c : ℤ, t = ((L + K : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    haveI : NeZero m := ⟨by omega⟩
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    set g := Nat.gcd 9 m
    have hmodg : B ≡ sigma10 B [MOD g] := by
      have h9 : (9 : ℤ) ∣ (sigma10 B : ℤ) - B :=
        Nat.ModEq.dvd (Nat.modEq_nine_digits_sum B)
      have hg9z : (g : ℤ) ∣ 9 :=
        Int.natCast_dvd_natCast.mpr hg9
      exact Nat.modEq_of_dvd (dvd_trans hg9z h9)
    have hcast : ZMod.castHom hgm (ZMod g) t =
        ((L + K : ℕ) : ZMod g) := by
      have hcv : ZMod.castHom hgm (ZMod g) v = 1 := by
        have hmul := congrArg (ZMod.castHom hgm (ZMod g)) hv
        rw [map_mul, map_one] at hmul
        have h10d : ZMod.castHom hgm (ZMod g)
            ((10 : ZMod m) ^ d) = 1 := by
          rw [map_pow]
          have h10g : ((10 : ℕ) : ZMod g) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
            exact (Nat.modEq_zero_iff_dvd.mpr hg9).add
              (Nat.ModEq.refl 1)
          rw [show (10 : ZMod m) = ((10 : ℕ) : ZMod m) from rfl,
              map_natCast, h10g, one_pow]
        rw [h10d, one_mul] at hmul
        exact hmul
      have hBg : ((B : ℕ) : ZMod g) =
          ((sigma10 B : ℕ) : ZMod g) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact hmodg
      have hLKg : ((L + K : ℕ) : ZMod g) =
          -((sigma10 B : ℕ) : ZMod g) := by
        have hsum : L + K + sigma10 B = s := by omega
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, hsum]
        exact (CharP.cast_eq_zero_iff (ZMod g) g s).mpr hgs
      rw [ht, map_mul, map_neg, map_natCast, hcv, mul_one,
          hBg, hLKg]
    set z := t - ((L + K : ℕ) : ZMod m)
    have hz : ZMod.castHom hgm (ZMod g) z = 0 := by
      rw [map_sub, hcast, map_natCast, sub_self]
    have hcv2 : ZMod.castHom hgm (ZMod g) z =
        ((z.val : ℕ) : ZMod g) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      rw [map_natCast]
    rw [hcv2] at hz
    have hdv : g ∣ z.val :=
      (CharP.cast_eq_zero_iff (ZMod g) g z.val).mp hz
    refine ⟨((z.val / g : ℕ) : ℤ), ?_⟩
    have ht2 : t = ((L + K : ℕ) : ZMod m) + z :=
      (add_sub_cancel _ _).symm
    rw [ht2]; congr 1
    rw [Int.cast_natCast, ← Nat.cast_mul,
        Nat.mul_div_cancel' hdv, ZMod.natCast_zmod_val]
  obtain ⟨u, hu8, huK, hut⟩ := hcov t hcosB
  refine middle_step R m B d s hRc hR10 hRB hBl hB0 L u hu8
    ?_ ?_
  · rw [hut]; exact htgt
  · have hfs := fibre_sigma u L hu8
    rw [huK] at hfs
    have : sigma10 B + (L + K) = s := by omega
    rw [hfs]; omega

/-- Variante de analytic_budget a somme s : il suffit que
    5*(m/9+7) <= s - sigma B. -/
theorem middle_budget (s m : ℕ)
    (hm10 : Nat.Coprime m 10) (hm1 : 1 < m)
    (σB : ℕ) (hσm : 5 * (m / 9 + 7) ≤ s - σB) (hσn : σB ≤ s)
    (L : ℕ) (hL : L = (s - σB) / 5) (t : ZMod m)
    (hcos : ∃ c : ℤ, t = ((s - σB : ℕ) : ZMod m) +
        ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m)) :
    ∃ u : ℕ → ℕ, (∀ e < L, u e ≤ 8) ∧
      ((List.range L).map u).sum = s - σB - L ∧
      (fibre u L : ZMod m) = t := by
  obtain ⟨C, hCb, hcov⟩ := coverage m hm10 t
  have hCL : C ≤ L := by
    rw [hL]; omega
  set r0 := (s - σB) % 5 with hr0
  have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
  obtain ⟨u, hu8, husum, hval⟩ := hcov L hCL r0 hr04 (by
    obtain ⟨c, hc⟩ := hcos
    refine ⟨c, ?_⟩
    have h5r : (5 * L + r0 : ℕ) = s - σB := by
      have := Nat.div_add_mod (s - σB) 5
      rw [hL, hr0]; omega
    rw [h5r]; exact hc)
  refine ⟨u, hu8, ?_, hval⟩
  have hdmod := Nat.div_add_mod (s - σB) 5
  rw [husum]; omega

/-- Budget : pour n >= 500 on a
    5*(n/9+7) + (n/8+8) + 18*len(n) <= n. -/
theorem budget_500 (n : ℕ) (hn : 500 ≤ n) :
    5 * (n / 9 + 7) + (n / 8 + 8) +
      18 * (Nat.digits 10 n).length ≤ n := by
  have hlog : Nat.log 10 n ≤ n / 125 := log10_le_125 n hn
  have hlen : (Nat.digits 10 n).length = Nat.log 10 n + 1 :=
    Nat.length_digits 10 n (by norm_num) (by omega)
  omega

/-- Existence du bloc milieu pour n >= 500 :
    m' | c et sigma(c) = n - 2*sigma(n). -/
theorem middle_large (n : ℕ) (hn : 500 ≤ n) :
    ∃ c : ℕ,
      (n / Nat.gcd n (10 ^ (Nat.digits 10 n).length)) ∣ c ∧
      sigma10 c + 2 * sigma10 n = n := by
  set d := (Nat.digits 10 n).length with hd
  set g := Nat.gcd n (10 ^ d) with hg
  set m' := n / g with hm'
  have hn0 : n ≠ 0 := by omega
  have hgpos : 0 < g := by
    rw [hg]; exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgm : n = g * m' := by
    rw [hm', mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n _)).symm
  have hm'1 : 1 ≤ m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hgm; omega
    · exact h
  have h10 : ¬ 10 ∣ m' := mp_not10 n (by omega)
  obtain ⟨R, m, D, hdecomp, hm10, hR10, hRc, hR25⟩ :=
    decomp_Rm m' (by omega) h10
  have hm'n : m' ≤ n := Nat.div_le_self n g
  -- Bloc B selon la forme de R = 2^D ou 5^D (D = 0 -> R = 1)
  obtain ⟨B, dB, hRB, hBl, hB0, hR10d, hσB8⟩ :
      ∃ B dB : ℕ, R ∣ B ∧ (Nat.digits 10 B).length = dB ∧
        B ≠ 0 ∧ R ∣ 10 ^ dB ∧ sigma10 B ≤ n / 8 + 8 := by
    rcases hR25 with rfl | rfl
    · rcases Nat.eq_zero_or_pos D with rfl | hD
      · have hsig1 : sigma10 1 = 1 := by
          norm_num [sigma10, Nat.digits, Nat.digitsAux]
        refine ⟨1, 1, by norm_num, ?_, by norm_num, by norm_num,
            by omega⟩
        norm_num [Nat.digits, Nat.digitsAux]
      · obtain ⟨B, hRB, hBl, -, hσB⟩ := lowBlock2 D hD
        have hB0 : B ≠ 0 := by
          rintro rfl; simp at hBl; omega
        have h2D : 2 ^ D ≤ n :=
          le_trans (Nat.le_of_dvd hm'1 ⟨m, hdecomp⟩) hm'n
        refine ⟨B, D, hRB, hBl, hB0,
          pow_dvd_pow_of_dvd (by norm_num) D, ?_⟩
        have hDle : D ≤ Nat.log 2 n :=
          le_log2_of_pow_le hn0 h2D
        have hlog := log2_le_div16 n (by omega)
        omega
    · rcases Nat.eq_zero_or_pos D with rfl | hD
      · have hsig1 : sigma10 1 = 1 := by
          norm_num [sigma10, Nat.digits, Nat.digitsAux]
        refine ⟨1, 1, by norm_num, ?_, by norm_num, by norm_num,
            by omega⟩
        norm_num [Nat.digits, Nat.digitsAux]
      · obtain ⟨B, hRB, hBl, -, hσB⟩ := lowBlock5 D hD
        have hB0 : B ≠ 0 := by
          rintro rfl; simp at hBl; omega
        have h5D : 5 ^ D ≤ n :=
          le_trans (Nat.le_of_dvd hm'1 ⟨m, hdecomp⟩) hm'n
        refine ⟨B, D, hRB, hBl, hB0,
          pow_dvd_pow_of_dvd (by norm_num) D, ?_⟩
        have hDle : D ≤ Nat.log 5 n :=
          Nat.le_log_of_pow_le (by norm_num) h5D
        have hlog := log5_le_100 n (by omega)
        omega
  -- somme cible s = n - 2*sigma(n)
  set s := n - 2 * sigma10 n
  have hsdef : s = n - 2 * sigma10 n := rfl
  have hσn9 : sigma10 n ≤ 9 * d := by
    rw [hd]; exact sigma10_le_9len n
  have hb := budget_500 n hn
  have hm'm : m ≤ m' := Nat.le_of_dvd hm'1
    ⟨R, by rw [hdecomp]; ring⟩
  have hmn : m ≤ n := le_trans hm'm hm'n
  have hσBs : sigma10 B ≤ s := by
    rw [hd] at hσn9; omega
  -- g | s car g | n et sigma(n) ≡ n (mod 9)
  have hgs : Nat.gcd 9 m ∣ s := by
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hg9m : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    have hgm' : Nat.gcd 9 m ∣ m' :=
      hg9m.trans ⟨R, by rw [mul_comm]; exact hdecomp⟩
    have hgn : Nat.gcd 9 m ∣ n :=
      hgm'.trans ⟨g, by rw [hgm]; ring⟩
    have hmod : sigma10 n ≡ n [MOD Nat.gcd 9 m] := by
      have h9 := Nat.modEq_nine_digits_sum n
      exact (h9.of_dvd hg9).symm
    have hσg : sigma10 n ≡ 0 [MOD Nat.gcd 9 m] :=
      hmod.trans (Nat.modEq_zero_iff_dvd.mpr hgn)
    have hσn : Nat.gcd 9 m ∣ sigma10 n :=
      Nat.modEq_zero_iff_dvd.mp hσg
    have h2σ : Nat.gcd 9 m ∣ 2 * sigma10 n := hσn.mul_left 2
    -- g | n - 2*sigma(n) par factorisation explicite
    obtain ⟨a, ha⟩ := hgn
    obtain ⟨b, hb2⟩ := h2σ
    have hg9pos : 0 < Nat.gcd 9 m := Nat.gcd_pos_of_pos_left m (by omega)
    have hba : b ≤ a := by
      have hle : Nat.gcd 9 m * b ≤ Nat.gcd 9 m * a := by
        rw [← hb2, ← ha]; omega
      exact Nat.le_of_mul_le_mul_left hle hg9pos
    refine ⟨a - b, ?_⟩
    have hdist : Nat.gcd 9 m * (a - b) =
        Nat.gcd 9 m * a - Nat.gcd 9 m * b :=
      Nat.mul_sub_left_distrib _ a b
    rw [hsdef, hb2, ha, hdist]
  have hbud : 5 * (m / 9 + 7) ≤ s - sigma10 B := by
    have h1 : 5 * (m / 9 + 7) ≤ 5 * (n / 9 + 7) := by
      have hdiv : m / 9 ≤ n / 9 := Nat.div_le_div_right hmn
      omega
    omega
  set L := (s - sigma10 B) / 5
  have hLdef : L = (s - sigma10 B) / 5 := rfl
  set r0 := (s - sigma10 B) % 5
  have hr04 : r0 ≤ 4 := Nat.lt_succ_iff.mp
    (Nat.mod_lt _ (by norm_num))
  by_cases hm1 : 1 < m
  · obtain ⟨c, hdiv, hsg⟩ := middle_Rm s R m hRc hm10 dB hR10d
      B hRB hBl hB0 hσBs hgs L (s - sigma10 B - L) (by omega)
      hm1 (fun t hcost =>
        middle_budget s m hm10 hm1 (sigma10 B) hbud hσBs
          L rfl t (by
            have heq : L + (s - sigma10 B - L) =
                s - sigma10 B := by omega
            obtain ⟨c, hc⟩ := hcost
            refine ⟨c, ?_⟩
            rw [show ((L + (s - sigma10 B - L) : ℕ) : ZMod m) =
              ((s - sigma10 B : ℕ) : ZMod m) from by rw [heq]]
              at hc
            exact hc))
    exact ⟨c, hdecomp ▸ hdiv, by omega⟩
  · have hm10' : m = 1 := by
      have hpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hdecomp; omega
        · exact h
      omega
    subst hm10'
    obtain ⟨u, hu8, huK⟩ := fibre_u_exists L (by omega) r0 hr04
    obtain ⟨c, hdiv, hsg⟩ := middle_step R 1 B dB s hRc hR10d
      hRB hBl hB0 L u hu8 (Subsingleton.elim _ _) (by
        have hfs := fibre_sigma u L hu8
        rw [huK] at hfs
        have h5r : 5 * L + r0 = s - sigma10 B :=
          Nat.div_add_mod _ 5
        omega)
    exact ⟨c, hdecomp ▸ hdiv, by omega⟩

/-- Si `p` est à la fois préfixe et suffixe de `l` avec `2·|p| ≤ |l|`,
alors `l = p ++ mid ++ p` pour un bloc médian `mid`. -/
theorem prefix_suffix_mid {p l : List ℕ} (hp : p <+: l) (hs : p <:+ l)
    (hlen : 2 * p.length ≤ l.length) : ∃ mid, l = p ++ mid ++ p := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hs
  have hla : a.length = l.length - p.length := by
    have := congrArg List.length ha
    simp [List.length_append] at this; omega
  have hlb : b.length = l.length - p.length := by
    have := congrArg List.length hb
    simp [List.length_append] at this; omega
  have hd : List.drop (l.length - p.length) l = p := by
    have h : List.drop b.length (b ++ p) = p := List.drop_left
    rw [hb, hlb] at h; exact h
  set n := a.length - p.length with hn_def
  have hda : List.drop n a = p := by
    have hd' : List.drop a.length l = p := by rw [hla]; exact hd
    have ha_eq : a = List.drop p.length l := by
      have h : List.drop p.length (p ++ a) = a := List.drop_left
      rw [ha] at h; exact h.symm
    have e2 : p.length + n = a.length := by omega
    rw [ha_eq, List.drop_drop, e2]
    exact hd'
  refine ⟨a.take n, ?_⟩
  have hsplit : a = a.take n ++ a.drop n :=
    (List.take_append_drop n a).symm
  calc l = p ++ a := ha.symm
    _ = p ++ (a.take n ++ a.drop n) := by rw [← hsplit]
    _ = p ++ (a.take n ++ p) := by rw [hda]
    _ = p ++ a.take n ++ p := by rw [← List.append_assoc]

/-- `alternatingSum` en récursion simple (définition par paires). -/
theorem alternatingSum_cons (a : ℤ) (l : List ℤ) :
    (a :: l).alternatingSum = a - l.alternatingSum := by
  induction l generalizing a with
  | nil => simp [List.alternatingSum, sub_eq_add_neg]
  | cons b t ih =>
    cases t with
    | nil => simp [List.alternatingSum, sub_eq_add_neg]
    | cons c u =>
      show a + -b + (c :: u).alternatingSum =
        a - (b :: c :: u).alternatingSum
      rw [ih b]; ring

/-- Majoration de la somme alternée par la somme des chiffres. -/
theorem altSum_abs_le (l : List ℕ) :
    |(l.map fun (e : ℕ) => (e : ℤ)).alternatingSum| ≤ (l.sum : ℤ) := by
  induction l with
  | nil => simp [List.alternatingSum]
  | cons d ds ih =>
    show |((d : ℤ) :: (ds.map fun (e : ℕ) => (e : ℤ))).alternatingSum| ≤
        ((d :: ds).sum : ℤ)
    rw [alternatingSum_cons, List.sum_cons]
    calc |(d : ℤ) - (ds.map fun (e : ℕ) => (e : ℤ)).alternatingSum|
        ≤ |(d : ℤ)| + |(ds.map fun (e : ℕ) => (e : ℤ)).alternatingSum| :=
          abs_sub _ _
      _ ≤ (d : ℤ) + (ds.sum : ℤ) := by
          rw [abs_of_nonneg (Int.natCast_nonneg d)]
          omega
      _ = ((d + ds.sum : ℕ) : ℤ) := by push_cast; ring

/-- La somme alternée a la parité de la somme des chiffres. -/
theorem altSum_modEq_two (l : List ℕ) :
    (l.map fun (e : ℕ) => (e : ℤ)).alternatingSum ≡ (l.sum : ℤ) [ZMOD 2] := by
  induction l with
  | nil => simp [List.alternatingSum, Int.ModEq]
  | cons d ds ih =>
    show ((d : ℤ) :: (ds.map fun (e : ℕ) => (e : ℤ))).alternatingSum ≡
        ((d :: ds).sum : ℤ) [ZMOD 2]
    rw [alternatingSum_cons, List.sum_cons]
    have hneg : ∀ x : ℤ, -x ≡ x [ZMOD 2] := by
      intro x
      have hd2 : (2 : ℤ) ∣ x - -x := ⟨x, by ring⟩
      exact Int.modEq_iff_dvd.mpr hd2
    have hs : (ds.sum : ℤ) ≡ -(ds.sum : ℤ) [ZMOD 2] := (hneg _).symm
    have e := (Int.ModEq.refl (d : ℤ)).sub (ih.trans hs)
    have hcast : ((d + ds.sum : ℕ) : ℤ) = (d : ℤ) + (ds.sum : ℤ) := by
      push_cast; ring
    rw [hcast]
    simpa [sub_neg_eq_add] using e

/-- Si `l.sum = 0`, tous les chiffres sont nuls et `ofDigits` vaut 0. -/
theorem ofDigits_eq_zero {l : List ℕ} (h : l.sum = 0) :
    Nat.ofDigits 10 l = 0 := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [List.sum_cons] at h
    have hd : d = 0 := by omega
    have hs : ds.sum = 0 := by omega
    calc Nat.ofDigits 10 (d :: ds) = d + 10 * Nat.ofDigits 10 ds := rfl
      _ = 0 + 10 * 0 := by rw [hd, ih hs]
      _ = 0 := by norm_num

/-- Un entier dont les chiffres (dans une écriture quelconque) somment à 1
est une puissance de 10. -/
theorem ofDigits_sum_one {l : List ℕ} (h : l.sum = 1) :
    ∃ j, Nat.ofDigits 10 l = 10 ^ j := by
  induction l with
  | nil => simp at h
  | cons d ds ih =>
    rw [List.sum_cons] at h
    rcases Nat.eq_zero_or_pos d with hd | hd
    · obtain ⟨j, hj⟩ := ih (by omega)
      refine ⟨j + 1, ?_⟩
      calc Nat.ofDigits 10 (d :: ds) = d + 10 * Nat.ofDigits 10 ds := rfl
        _ = 10 ^ (j + 1) := by rw [hd, hj]; ring
    · have hd1 : d = 1 := by omega
      have hs0 : ds.sum = 0 := by omega
      refine ⟨0, ?_⟩
      calc Nat.ofDigits 10 (d :: ds) = d + 10 * Nat.ofDigits 10 ds := rfl
        _ = 10 ^ 0 := by rw [hd1, ofDigits_eq_zero hs0]; ring

theorem A077739 (n : ℕ) (hn : 1 ≤ n) :
    (∃ N : ℕ, 0 < N ∧ n ∣ N ∧
      (Nat.digits 10 N).sum = n ∧
      Nat.digits 10 n <:+ Nat.digits 10 N ∧
      Nat.digits 10 n <+: Nat.digits 10 N) ↔
    n ∉ ({11, 17, 19} : Set ℕ) := by
  constructor
  · -- direction zero : n ∈ {11,17,19} -> pas de temoin
    rintro ⟨N, hN0, hdv, hsum, hsuf, hpre⟩ hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl
    · -- n = 11 : somme alternée de c ≡ 0 mod 11 impossible (|·| ≤ 7, impair)
      have hdn : Nat.digits 10 11 = [1, 1] := by decide
      rw [hdn] at hsuf hpre
      rcases lt_or_ge (Nat.digits 10 N).length 4 with hl | hl
      · obtain ⟨a, ha⟩ := hpre
        obtain ⟨b', hb'⟩ := hsuf
        rcases a with _ | ⟨x, a'⟩
        · rw [List.append_nil] at ha
          rw [← ha] at hsum; norm_num at hsum
        · rcases a' with _ | ⟨y, a''⟩
          · have hb1 : b'.length = 1 := by
              have := congrArg List.length hb'
              rw [← ha] at this; simp at this; omega
            obtain ⟨b0, hb0⟩ : ∃ b0, b' = [b0] := by
              rcases b' with _ | ⟨b0, b''⟩
              · simp at hb1
              · rcases b'' with _ | ⟨b2, b3⟩
                · exact ⟨b0, rfl⟩
                · simp at hb1
            rw [hb0] at hb'
            have e : ([b0, 1, 1] : List ℕ) = Nat.digits 10 N := hb'
            have e2 : ([1, 1, x] : List ℕ) = Nat.digits 10 N := ha
            have e3 := e.trans e2.symm
            simp only [List.cons.injEq] at e3
            rcases e3 with ⟨hb0e, -, hxe, -⟩
            subst hb0e; subst x
            rw [← ha] at hsum; norm_num at hsum
          · have := congrArg List.length ha
            simp at this; omega
      · obtain ⟨mid, hmid⟩ := prefix_suffix_mid hpre hsuf (by simp; omega)
        have hσmid : mid.sum = 7 := by
          rw [hmid] at hsum; simp [List.sum_append] at hsum; omega
        have hof : Nat.ofDigits 10 [1, 1] = 11 := by decide
        have hN : N = 11 + 100 * Nat.ofDigits 10 mid +
            11 * 10 ^ (mid.length + 2) := by
          conv_lhs => rw [← Nat.ofDigits_digits 10 N]
          rw [hmid]
          repeat rw [Nat.ofDigits_append]
          rw [hof]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          ring_nf
        have h11M : (11 : ℕ) ∣ Nat.ofDigits 10 mid := by
          obtain ⟨t, ht⟩ := hdv
          have hk : 11 * (t - (1 + 10 ^ (mid.length + 2))) =
              100 * Nat.ofDigits 10 mid := by omega
          exact (by decide : Nat.Coprime 11 100).dvd_of_dvd_mul_left
            ⟨t - (1 + 10 ^ (mid.length + 2)), hk.symm⟩
        -- 11 | ofDigits mid → somme alternée ≡ 0 mod 11
        have hcong : ((Nat.ofDigits (10 : ℕ) mid : ℕ) : ℤ) ≡
            (mid.map fun (e : ℕ) => (e : ℤ)).alternatingSum [ZMOD 11] := by
          have h1 : Nat.ofDigits (10 : ℤ) mid ≡
              Nat.ofDigits (-1 : ℤ) mid [ZMOD 11] :=
            Nat.ofDigits_zmodeq' 10 (-1) 11 (by decide) mid
          rw [Nat.ofDigits_neg_one] at h1
          rw [Nat.coe_ofDigits, Nat.cast_ofNat]
          exact h1
        have h11z : ((Nat.ofDigits (10 : ℕ) mid : ℕ) : ℤ) ≡ 0 [ZMOD 11] :=
          Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr h11M)
        have halt := hcong.symm.trans h11z
        have h11dvd : (11 : ℤ) ∣
            (mid.map fun (e : ℕ) => (e : ℤ)).alternatingSum :=
          Int.modEq_zero_iff_dvd.mp halt
        obtain ⟨k, hk⟩ := h11dvd
        have habs := altSum_abs_le mid
        rw [hσmid] at habs
        have hk0 : k = 0 := by
          rw [hk] at habs
          have h2 := abs_le.mp habs
          omega
        rw [hk0] at hk; simp at hk
        -- parité : alt ≡ 7 mod 2 mais alt = 0
        have hpar := altSum_modEq_two mid
        rw [hσmid, hk] at hpar
        exact absurd hpar (by decide)
    · -- n = 17 : σmid = 1 force c = 10^j, 17 ne divise pas
      have hdn : Nat.digits 10 17 = [7, 1] := by decide
      rw [hdn] at hsuf hpre
      rcases lt_or_ge (Nat.digits 10 N).length 4 with hl | hl
      · obtain ⟨a, ha⟩ := hpre
        obtain ⟨b', hb'⟩ := hsuf
        rcases a with _ | ⟨x, a'⟩
        · rw [List.append_nil] at ha
          rw [← ha] at hsum; norm_num at hsum
        · rcases a' with _ | ⟨y, a''⟩
          · have hb1 : b'.length = 1 := by
              have := congrArg List.length hb'
              rw [← ha] at this; simp at this; omega
            obtain ⟨b0, hb0⟩ : ∃ b0, b' = [b0] := by
              rcases b' with _ | ⟨b0, b''⟩
              · simp at hb1
              · rcases b'' with _ | ⟨b2, b3⟩
                · exact ⟨b0, rfl⟩
                · simp at hb1
            rw [hb0] at hb'
            have e : ([b0, 7, 1] : List ℕ) = Nat.digits 10 N := hb'
            have e2 : ([7, 1, x] : List ℕ) = Nat.digits 10 N := ha
            have e3 := e.trans e2.symm
            simp only [List.cons.injEq] at e3
            rcases e3 with ⟨-, h71, -⟩
            norm_num at h71
          · have := congrArg List.length ha
            simp at this; omega
      · obtain ⟨mid, hmid⟩ := prefix_suffix_mid hpre hsuf (by simp; omega)
        have hσmid : mid.sum = 1 := by
          rw [hmid] at hsum; simp [List.sum_append] at hsum; omega
        have hof : Nat.ofDigits 10 [7, 1] = 17 := by decide
        have hN : N = 17 + 100 * Nat.ofDigits 10 mid +
            17 * 10 ^ (mid.length + 2) := by
          conv_lhs => rw [← Nat.ofDigits_digits 10 N]
          rw [hmid]
          repeat rw [Nat.ofDigits_append]
          rw [hof]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          ring_nf
        have h17M : (17 : ℕ) ∣ Nat.ofDigits 10 mid := by
          obtain ⟨t, ht⟩ := hdv
          have hk : 17 * (t - (1 + 10 ^ (mid.length + 2))) =
              100 * Nat.ofDigits 10 mid := by omega
          exact (by decide : Nat.Coprime 17 100).dvd_of_dvd_mul_left
            ⟨t - (1 + 10 ^ (mid.length + 2)), hk.symm⟩
        obtain ⟨j, hj⟩ := ofDigits_sum_one hσmid
        rw [hj] at h17M
        have hcop : Nat.Coprime 17 (10 ^ j) :=
          Nat.Coprime.pow_right j (by decide : Nat.Coprime 17 10)
        have h1 : (17 : ℕ) ∣ Nat.gcd 17 (10 ^ j) :=
          Nat.dvd_gcd dvd_rfl h17M
        have hgc : Nat.gcd 17 (10 ^ j) = 1 := hcop
        rw [hgc] at h1
        exact absurd h1 (by decide)
    · -- n = 19 : σmid < 0 impossible
      have hdn : Nat.digits 10 19 = [9, 1] := by decide
      rw [hdn] at hsuf hpre
      rcases lt_or_ge (Nat.digits 10 N).length 4 with hl | hl
      · obtain ⟨a, ha⟩ := hpre
        obtain ⟨b', hb'⟩ := hsuf
        rcases a with _ | ⟨x, a'⟩
        · rw [List.append_nil] at ha
          rw [← ha] at hsum; norm_num at hsum
        · rcases a' with _ | ⟨y, a''⟩
          · have hb1 : b'.length = 1 := by
              have := congrArg List.length hb'
              rw [← ha] at this; simp at this; omega
            obtain ⟨b0, hb0⟩ : ∃ b0, b' = [b0] := by
              rcases b' with _ | ⟨b0, b''⟩
              · simp at hb1
              · rcases b'' with _ | ⟨b2, b3⟩
                · exact ⟨b0, rfl⟩
                · simp at hb1
            rw [hb0] at hb'
            have e : ([b0, 9, 1] : List ℕ) = Nat.digits 10 N := hb'
            have e2 : ([9, 1, x] : List ℕ) = Nat.digits 10 N := ha
            have e3 := e.trans e2.symm
            simp only [List.cons.injEq] at e3
            rcases e3 with ⟨-, h91, -⟩
            norm_num at h91
          · have := congrArg List.length ha
            simp at this; omega
      · obtain ⟨mid, hmid⟩ := prefix_suffix_mid hpre hsuf (by simp; omega)
        rw [hmid] at hsum
        simp [List.sum_append] at hsum
        omega
  · intro hmem
    have h11 : n ≠ 11 := by intro he; apply hmem; rw [he]; simp
    have h17 : n ≠ 17 := by intro he; apply hmem; rw [he]; simp
    have h19 : n ≠ 19 := by intro he; apply hmem; rw [he]; simp
    rcases lt_or_ge n 10 with h10 | h10
    · -- 1 <= n <= 9 : N = n
      refine ⟨n, hn, dvd_refl n, ?_, ?_, ?_⟩
      · rw [Nat.digits_of_lt 10 n (by omega) (by omega),
            List.sum_singleton]
      · exact ⟨[], by simp⟩
      · exact ⟨[], by simp⟩
    · by_cases hlt : n < 500
      · -- 10 <= n <= 499 : table de temoins
        obtain ⟨hdv, hsum⟩ := wit739_spec n h10 hlt h11 h17 h19
        exact exists_of_wit n (wit739 n) hn hdv hsum
      · -- n >= 500 : machinerie fibre (L3d + bloc mixte)
        obtain ⟨c, hdiv, hsum⟩ := middle_large n (by omega)
        exact exists_of_wit n c hn hdiv hsum

end OMA.A077740Port

open OMA.A077740Port in
theorem OMA.solution : type_of% @OMA.S_oeis_a077740.main := by
  intro n hn
  have key := A077739 n (by omega : 1 ≤ n)
  -- pont : pour 0 < n, a n = term739 n / n = 0 ssi term739 n = 0
  -- (term739 n > 0 implique n | term739 n, donc n <= term739 n)
  have hbr : OMA.S_oeis_a077740.a n = 0 ↔
      OMA.S_oeis_a077740.term739 n = 0 := by
    constructor
    · intro h0
      by_contra hne
      have hpos : 0 < OMA.S_oeis_a077740.term739 n := Nat.pos_of_ne_zero hne
      have hs : {m | OMA.S_oeis_a077740.qualifies n m}.Nonempty := by
        rcases Set.eq_empty_or_nonempty
            {m | OMA.S_oeis_a077740.qualifies n m} with hempty | hne'
        · rw [show OMA.S_oeis_a077740.term739 n =
              sInf {m | OMA.S_oeis_a077740.qualifies n m} from rfl,
              hempty, Nat.sInf_empty] at hpos
          exact absurd hpos (lt_irrefl 0)
        · exact hne'
      have hmem : OMA.S_oeis_a077740.qualifies n
          (OMA.S_oeis_a077740.term739 n) := Nat.sInf_mem hs
      obtain ⟨hm0, hmdvd, -, -, -⟩ := hmem
      have hle : n ≤ OMA.S_oeis_a077740.term739 n := Nat.le_of_dvd hm0 hmdvd
      have hdivpos : 0 < OMA.S_oeis_a077740.term739 n / n := Nat.div_pos hle hn
      rw [show OMA.S_oeis_a077740.a n =
          OMA.S_oeis_a077740.term739 n / n from rfl] at h0
      omega
    · intro h0
      rw [show OMA.S_oeis_a077740.a n =
          OMA.S_oeis_a077740.term739 n / n from rfl, h0]
      exact Nat.zero_div n
  rw [hbr]
  -- meme cloture sInf qu'a077739 : term739 n = 0 ssi n in {11,17,19}
  constructor
  · intro h0
    rw [show OMA.S_oeis_a077740.term739 n =
        sInf {m | OMA.S_oeis_a077740.qualifies n m} from rfl,
        Nat.sInf_eq_zero] at h0
    rcases h0 with h0mem | hempty
    · exfalso
      have hq : OMA.S_oeis_a077740.qualifies n 0 := h0mem
      rcases hq with ⟨hlt, -⟩
      exact absurd hlt (lt_irrefl 0)
    · have hnw : ¬ ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).sum = n ∧
          Nat.digits 10 n <:+ Nat.digits 10 N ∧
          Nat.digits 10 n <+: Nat.digits 10 N := by
        rintro ⟨N, hN0, hdv, hsum, hsuf, hpre⟩
        have hq : N ∈ {m | OMA.S_oeis_a077740.qualifies n m} :=
          ⟨hN0, hdv, hpre, hsuf, hsum⟩
        rw [hempty] at hq
        exact absurd hq (Set.notMem_empty N)
      have hmem : n ∈ ({11, 17, 19} : Set ℕ) := by
        by_contra hc
        exact hnw (key.mpr hc)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      exact hmem
  · intro hdis
    have hmem : n ∈ ({11, 17, 19} : Set ℕ) := by
      rcases hdis with rfl | rfl | rfl <;> simp
    have hnw : ¬ ∃ N : ℕ, 0 < N ∧ n ∣ N ∧ (Nat.digits 10 N).sum = n ∧
        Nat.digits 10 n <:+ Nat.digits 10 N ∧
        Nat.digits 10 n <+: Nat.digits 10 N :=
      fun h => key.mp h hmem
    have hempty : {m | OMA.S_oeis_a077740.qualifies n m} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro m hq
      obtain ⟨h0m, hdv, hpre, hsuf, hsum⟩ := hq
      exact hnw ⟨m, h0m, hdv, hsum, hsuf, hpre⟩
    rw [show OMA.S_oeis_a077740.term739 n =
        sInf {m | OMA.S_oeis_a077740.qualifies n m} from rfl, hempty]
    exact Nat.sInf_empty
