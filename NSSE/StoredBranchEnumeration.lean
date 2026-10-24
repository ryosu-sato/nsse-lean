import NSSE.StoredOutsideController

/-! Counted endpoint and branch enumeration of the next-rank row family.
`UnifiedBlockPresentation.branches` is produced by actual recursive list
construction, and each branch index is turned into the stored row of
`StoredOutsideController`. -/
namespace NSSE.StoredBranchEnumeration
open SymbolicGuardedBlocks GuardedRowFiring
open CountedListConstruction
variable {k : Nat} {n : Nat}

/-! ### Endpoints -/

def row1 (r0 r1 t0 : Fin n) (js : List (Fin n)) : List (Ends n) × Nat :=
  map (fun t1 => ((⟨r0,r1,t0,t1⟩ : Ends n),5)) js
def row2 (r0 r1 : Fin n) (js : List (Fin n)) : List (Ends n) × Nat :=
  flatMap (fun t0 => row1 r0 r1 t0 js) js
def row3 (r0 : Fin n) (js : List (Fin n)) : List (Ends n) × Nat :=
  flatMap (fun r1 => row2 r0 r1 js) js
def row4 (js : List (Fin n)) : List (Ends n) × Nat :=
  flatMap (fun r0 => row3 r0 js) js

theorem row1_value (r0 r1 t0 : Fin n) (js : List (Fin n)) :
    (row1 r0 r1 t0 js).1 = js.map (fun t1 => (⟨r0,r1,t0,t1⟩ : Ends n)) := map_value _ _
theorem row2_value (r0 r1 : Fin n) (js : List (Fin n)) :
    (row2 r0 r1 js).1 = js.flatMap (fun t0 => js.map (fun t1 => (⟨r0,r1,t0,t1⟩ : Ends n))) := by
  simp only [row2,flatMap_value,row1_value]
theorem row3_value (r0 : Fin n) (js : List (Fin n)) :
    (row3 r0 js).1 =
      js.flatMap (fun r1 => js.flatMap (fun t0 => js.map (fun t1 => (⟨r0,r1,t0,t1⟩ : Ends n)))) := by
  simp only [row3,flatMap_value,row2_value]
theorem row4_value (js : List (Fin n)) :
    (row4 js).1 = js.flatMap (fun r0 => js.flatMap (fun r1 =>
      js.flatMap (fun t0 => js.map (fun t1 => (⟨r0,r1,t0,t1⟩ : Ends n))))) := by
  simp only [row4,flatMap_value,row3_value]

theorem row1_length (r0 r1 t0 : Fin n) (js : List (Fin n)) :
    (row1 r0 r1 t0 js).1.length = js.length := by simp [row1_value]
theorem row2_length (r0 r1 : Fin n) (js : List (Fin n)) :
    (row2 r0 r1 js).1.length = js.length^2 := by
  simp [row2_value,List.length_flatMap,List.map_const',List.sum_replicate,smul_eq_mul,
    Nat.pow_two]
theorem row3_length (r0 : Fin n) (js : List (Fin n)) :
    (row3 r0 js).1.length = js.length^3 := by
  simp only [row3,flatMap_value]
  rw [List.length_flatMap]
  simp [row2_length,List.map_const',List.sum_replicate,smul_eq_mul]
  ring
theorem row4_length (js : List (Fin n)) : (row4 js).1.length = js.length^4 := by
  simp only [row4,flatMap_value]
  rw [List.length_flatMap]
  simp [row3_length,List.map_const',List.sum_replicate,smul_eq_mul]
  ring

def b1 (L : Nat) := 1+L*6
def b2 (L : Nat) := 1+L*(2+b1 L+L)
def b3 (L : Nat) := 1+L*(2+b2 L+L^2)
def b4 (L : Nat) := 1+L*(2+b3 L+L^3)

theorem row1_bound (r0 r1 t0 : Fin n) (js : List (Fin n)) : (row1 r0 r1 t0 js).2 ≤ b1 js.length := by
  have h := map_bound (fun t1 => ((⟨r0,r1,t0,t1⟩ : Ends n),5)) js 5 (fun _ _ => le_rfl)
  simp only [row1,b1]; omega
theorem row2_bound (r0 r1 : Fin n) (js : List (Fin n)) : (row2 r0 r1 js).2 ≤ b2 js.length :=
  flatMap_bound _ js (b1 js.length) js.length (fun t0 _ => row1_bound r0 r1 t0 js)
    (fun t0 _ => (row1_length r0 r1 t0 js).le)
theorem row3_bound (r0 : Fin n) (js : List (Fin n)) : (row3 r0 js).2 ≤ b3 js.length :=
  flatMap_bound _ js (b2 js.length) (js.length^2) (fun r1 _ => row2_bound r0 r1 js)
    (fun r1 _ => (row2_length r0 r1 js).le)
theorem row4_bound (js : List (Fin n)) : (row4 js).2 ≤ b4 js.length :=
  flatMap_bound _ js (b3 js.length) (js.length^3) (fun r0 _ => row3_bound r0 js)
    (fun r0 _ => (row3_length r0 js).le)

def endpointEntries (n : Nat) : List (Ends n) × Nat :=
  let a := CountedFinEnumeration.enumerate n
  let b := row4 a.1
  (b.1,1+a.2+b.2)

theorem endpointEntries_value (n : Nat) :
    (endpointEntries n).1 = UnifiedBlockPresentation.endpoints n := by
  simp only [endpointEntries,row4_value,CountedFinEnumeration.value,
    UnifiedBlockPresentation.endpoints]

theorem endpointEntries_length (n : Nat) : (endpointEntries n).1.length = n^4 := by
  simp only [endpointEntries]
  rw [row4_length,CountedFinEnumeration.value,List.length_finRange]

def endpointBudget (n : Nat) := 1+(n+1)^2+b4 n
theorem endpointEntries_bound (n : Nat) : (endpointEntries n).2 ≤ endpointBudget n := by
  have ha := CountedFinEnumeration.bound n
  have hb := row4_bound (CountedFinEnumeration.enumerate n).1
  have hl : (CountedFinEnumeration.enumerate n).1.length = n := by
    rw [CountedFinEnumeration.value,List.length_finRange]
  rw [hl] at hb
  simp only [endpointEntries,endpointBudget]; omega

theorem endpointBudget_mono {a b : Nat} (h : a ≤ b) : endpointBudget a ≤ endpointBudget b := by
  unfold endpointBudget b4 b3 b2 b1
  gcongr

/-! ### Branches -/

abbrev Branch (ns : Fin k → Nat) := UnifiedBlockPresentation.Branch ns

def pairOf (ns : Fin k → Nat) (i : Fin k) (e : Ends (ns i)) : List (Branch ns) × Nat :=
  ([⟨i,e,false⟩,⟨i,e,true⟩],5)

def branchOf (ns : Fin k → Nat) (i : Fin k) : List (Branch ns) × Nat :=
  let a := endpointEntries (ns i)
  let b := flatMap (pairOf ns i) a.1
  (b.1,1+a.2+b.2)

theorem branchOf_value (ns : Fin k → Nat) (i : Fin k) :
    (branchOf ns i).1 = (UnifiedBlockPresentation.endpoints (ns i)).flatMap
      (fun e => [⟨i,e,false⟩,⟨i,e,true⟩]) := by
  simp only [branchOf,flatMap_value,endpointEntries_value,pairOf]

theorem branchOf_length (ns : Fin k → Nat) (i : Fin k) :
    (branchOf ns i).1.length = 2*(ns i)^4 := by
  rw [branchOf_value,List.length_flatMap]
  simp [List.map_const',List.sum_replicate,smul_eq_mul,
    UnifiedBlockPresentation.endpoints,List.length_flatMap,Nat.mul_comm]
  ring

def branchOfBudget (N : Nat) := 2+endpointBudget N+2*N^4*9
theorem branchOf_bound (ns : Fin k → Nat) (i : Fin k) (N : Nat) (hN : ns i ≤ N) :
    (branchOf ns i).2 ≤ branchOfBudget N := by
  have ha := (endpointEntries_bound (ns i)).trans (endpointBudget_mono hN)
  have hb := flatMap_bound (pairOf ns i) (endpointEntries (ns i)).1 5 2
    (fun _ _ => le_rfl) (fun _ _ => by simp [pairOf])
  rw [endpointEntries_length] at hb
  have hp : (ns i)^4 ≤ N^4 := Nat.pow_le_pow_left hN 4
  simp only [branchOf,branchOfBudget]; omega

def branchEntries (ns : Fin k → Nat) : List (Branch ns) × Nat :=
  let a := CountedFinEnumeration.enumerate k
  let b := flatMap (branchOf ns) a.1
  (b.1,1+a.2+b.2)

theorem branchEntries_value (ns : Fin k → Nat) :
    (branchEntries ns).1 = UnifiedBlockPresentation.branches ns := by
  simp only [branchEntries,flatMap_value,CountedFinEnumeration.value,branchOf_value,
    UnifiedBlockPresentation.branches]

def branchBudget (k N : Nat) := 2+(k+1)^2+k*(2+branchOfBudget N+2*N^4)
theorem branchEntries_bound (ns : Fin k → Nat) (N : Nat) (hN : ∀ i, ns i ≤ N) :
    (branchEntries ns).2 ≤ branchBudget k N := by
  have ha := CountedFinEnumeration.bound k
  have hl : (CountedFinEnumeration.enumerate k).1.length = k := by
    rw [CountedFinEnumeration.value,List.length_finRange]
  have hb := flatMap_bound (branchOf ns) (CountedFinEnumeration.enumerate k).1
    (branchOfBudget N) (2*N^4) (fun i _ => branchOf_bound ns i N (hN i))
    (fun i _ => by
      rw [branchOf_length]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hN i) 4))
  rw [hl] at hb
  simp only [branchEntries,branchBudget]; omega

structure Table (ns : Fin k → Nat) where
  count : Nat
  values : StoredRelationTuple.Data (Branch ns) count
  count_eq : count = (UnifiedBlockPresentation.branches ns).length
  values_eq : values.values = UnifiedBlockPresentation.branches ns

def build (ns : Fin k → Nat) : Table ns × Nat :=
  let a := branchEntries ns
  let c := CountedSupportRule.add a.1.length 0
  have hc : c.1 = (UnifiedBlockPresentation.branches ns).length := by
    simp only [c,a,CountedSupportRule.add_value,Nat.add_zero,branchEntries_value]
  (⟨c.1,⟨a.1,by rw [branchEntries_value,← hc]⟩,hc,branchEntries_value ns⟩,2+a.2+c.2)

theorem build_bound (ns : Fin k → Nat) (N : Nat) (hN : ∀ i, ns i ≤ N) :
    (build ns).2 ≤ 3+branchBudget k N+(branchEntries ns).1.length := by
  have ha := branchEntries_bound ns N hN
  simp only [build,CountedSupportRule.add_cost]; omega

def read (T : Table ns) (j : Fin T.count) : Branch ns × Nat := StoredRelationTuple.read T.values j
theorem read_value (T : Table ns) (j : Fin T.count) :
    (read T j).1 = UnifiedBlockPresentation.branchAt ns (Fin.cast T.count_eq j) := by
  simp only [read,StoredRelationTuple.read_value,UnifiedBlockPresentation.branchAt,
    List.get_eq_getElem,T.values_eq]
  rfl
theorem read_bound (T : Table ns) (j : Fin T.count) : (read T j).2 ≤ T.count :=
  StoredRelationTuple.read_bound T.values j

/-! ### The stored family -/

/-- The stored firing row of one enumerated branch. -/
def rowOf (ns : Fin k → Nat) (c : Nat) (b : Branch ns) :
    StoredOutsideController.Result ns c b.1 × Nat :=
  StoredOutsideController.build ns b.1 (c := c) b.2.1 b.2.2

theorem rowOf_bound (ns : Fin k → Nat) (c : Nat) (b : Branch ns) :
    (rowOf ns c b).2 ≤ 614*((ns b.1)+1)^3 :=
  StoredOutsideController.polynomial ns b.1 b.2.1 b.2.2

theorem rowOf_states (ns : Fin k → Nat) (c : Nat) (b : Branch ns) :
    (rowOf ns c b).1.states.count = 4*(ns b.1)+2 :=
  StoredOutsideController.build_states ns b.1 b.2.1 b.2.2

theorem rowOf_fires (ns : Fin k → Nat) (c : Nat)
    (j : Fin (UnifiedBlockPresentation.branches ns).length) {D : Type}
    [(UnifiedBlockPresentation.language ns c).Structure D] (v : Empty → D)
    (seed : D) (body : List D) :
    Fires (rowOf ns c (UnifiedBlockPresentation.branchAt ns j)).1.row.original v seed body ↔
      Fires (UnifiedBlockPresentation.familyRows ns c j) v seed body :=
  StoredOutsideController.build_fires ns _ _ _ v seed body

/-- The enumerated stored rows decide avoidance of the whole original family. -/
theorem avoids_stored_family {L : FirstOrder.Language} {P : Type} {c : Nat}
    (ns : Fin k → Nat) (rows : (i : Fin k) → SymbolicGuardedBlocks.Row L P (ns i))
    (C : SymbolicGuardedBlocks.Row L P c) (seed last : P) {D : Type} [L.Structure D] (p : P → D)
    (bs : List (List D)) (hNoA : TerminalCutGeometry.NoA (p last) bs) :
    (∀ i, ¬ PositiveFires (rows i) p (p seed) (TerminalBorderRank.decodeBlocks (p last) bs)) ↔
      letI := UnifiedBlockPresentation.model rows C seed last p
      ∀ j : Fin (UnifiedBlockPresentation.branches ns).length,
        ¬ Fires (rowOf ns c (UnifiedBlockPresentation.branchAt ns j)).1.row.original
            (Empty.elim : Empty → List D) (bs.head?.getD []) bs.tail := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  rw [UnifiedBlockPresentation.avoids_enumerated_family rows C seed last p bs hNoA]
  exact forall_congr' (fun j => not_congr
    (rowOf_fires ns c j (Empty.elim : Empty → List D) _ _).symm)
end NSSE.StoredBranchEnumeration
