import NSSE.MultiVarianceTokenCompleteness

/-! Exact original support crossings at every proper and terminal rail
position.  The shared off-path fill slots are explicitly excluded from
the exactness theorem; their universal annotation is only an invariant. -/
namespace NSSE.MultiVarianceTokenExact
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceModelTokens (Tokens State)
open MultiVarianceSpineTokens MultiVarianceSpineSeparation MultiVarianceOriginalSpine
open MultiVarianceSpineCrossings MultiVarianceSpineRows MultiVarianceSpineNormal
open MultiVarianceSupportNormal MultiVarianceTokenCompleteness
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n m : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)
variable (theta : Constraints arity m) (oldMap : Fin n → Fin m)

theorem roots_row (s : Spine arity) (f : Fin (width s.depth) → Fin m) (S : State n)
    (hX : Crosses pol theta oldMap false (f (rootX s.depth)) S.1)
    (hY : Crosses pol theta oldMap true (f (rootY s.depth)) S.2)
    (r : Bool) (k : Fin (width s.depth)) (hk : k.val < 2) (hp : k.val%2 = parity r) :
    Crosses pol theta oldMap r (f k) (rowSlot pol phi s S k.val) := by
  by_cases h0 : k.val = 0
  · have he : k = rootX s.depth := Fin.ext h0
    subst k
    cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true,rootX,Fin.val_mk] at hp
    · simpa only [rootX,Fin.val_mk,rowSlot_zero] using hX
    · omega
  · have h1 : k.val = 1 := by omega
    have he : k = rootY s.depth := Fin.ext h1
    subst k
    cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true,rootY,Fin.val_mk] at hp
    · omega
    · simpa only [rootY,Fin.val_mk,rowSlot_one] using hY

theorem allCrossings_row (s : Spine arity) (f : Fin (width s.depth) → Fin m) (S : State n)
    (hc : AllCrossings pol phi theta oldMap s f S) (r : Bool) (k : Fin (width s.depth))
    (hk : k.val < 2*s.depth+2) (hp : k.val%2 = parity r) :
    Crosses pol theta oldMap r (f k) (rowSlot pol phi s S k.val) := by
  induction s generalizing S with
  | stop a b => exact roots_row pol phi theta oldMap _ f S hc.1 hc.2 r k hk hp
  | step h i s ih =>
    by_cases hsmall : k.val < 2
    · exact roots_row pol phi theta oldMap _ f S hc.1.1 hc.1.2 r k hsmall hp
    have h0 : k.val ≠ 0 := by omega
    have h1 : k.val ≠ 1 := by omega
    let j : Fin (width s.depth) := ⟨k.val-2,by have hi := k.isLt; simp only [width,Spine.depth] at hi ⊢; omega⟩
    have he : shift s.depth j = k := by apply Fin.ext; dsimp only [shift,j]; omega
    have hj : j.val < 2*s.depth+2 := by dsimp only [j]; simp only [Spine.depth] at hk; omega
    have hjp : j.val%2 = parity r := by dsimp only [j]; omega
    have hr := ih (fun t => f (shift s.depth t)) (move pol phi S h i) hc.2 j hj hjp
    simp only [he] at hr
    simpa only [rowSlot,h0,h1,if_false,j] using hr

/-- Exact at every rail slot, including the terminal pair. -/
theorem support_iff_row (Q : Query arity n) (s : Spine arity) (r : Bool) (k : Fin (width s.depth))
    (hk : k.val < 2*s.depth+2) (hp : k.val%2 = parity r) (z : Fin n) :
    (if r then Support pol (extension pol Q s) (old s.depth z) (slot Q.left Q.right s.depth k)
      else Support pol (extension pol Q s) (slot Q.left Q.right s.depth k) (old s.depth z)) ↔
      z ∈ rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) k.val := by
  constructor
  · intro hs
    have hc : Crossing pol Q.constraints (seeds pol Q s) (old s.depth) r
        (slot Q.left Q.right s.depth k) z := by
      cases r
      · exact (extension_lower_crossing_iff pol Q s _ z).mp hs
      · exact (extension_upper_crossing_iff pol Q s _ z).mp hs
    have hm := crossing_annotation pol Q s hc
    rw [annotation_slot pol Q s r k hp] at hm
    exact hm
  · intro hz
    exact allCrossings_row pol Q.constraints (extension pol Q s) (old s.depth) s
      (slot Q.left Q.right s.depth) _ (extension_crossings pol Q s) r k hk hp z hz

/-- Every original-variable-mediated birth, with no physical-side pruning. -/
theorem birth_iff_rows (Q : Query arity n) (s : Spine arity) (k l : Fin (width s.depth))
    (hk : k.val < 2*s.depth+2) (hl : l.val < 2*s.depth+2) (kp : k.val%2 = 0) (lp : l.val%2 = 1) :
    (∃ z, Support pol (extension pol Q s) (slot Q.left Q.right s.depth k) (old s.depth z) ∧
      Support pol (extension pol Q s) (old s.depth z) (slot Q.left Q.right s.depth l)) ↔
    (rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) k.val ∩
      rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) l.val).Nonempty := by
  constructor
  · rintro ⟨z,hkz,hzl⟩
    exact ⟨z,Finset.mem_inter.mpr ⟨(support_iff_row pol Q s false k hk kp z).mp hkz,
      (support_iff_row pol Q s true l hl lp z).mp hzl⟩⟩
  · rintro ⟨z,hz⟩
    obtain ⟨hzk,hzl⟩ := Finset.mem_inter.mp hz
    exact ⟨z,(support_iff_row pol Q s false k hk kp z).mpr hzk,
      (support_iff_row pol Q s true l hl lp z).mpr hzl⟩

def path : Spine arity → List (Letter arity)
  | .stop _ _ => []
  | .step h i s => ⟨h,i⟩ :: path s

omit [DecidableEq H] in
@[simp] theorem path_length (s : Spine arity) : (path s).length = s.depth := by
  induction s <;> simp_all [path,Spine.depth]

theorem rowSlot_run (s : Spine arity) (S : State n) (d : Nat) (hd : d ≤ s.depth) :
    rowSlot pol phi s S (2*d) = (runRoles pol phi S ((path s).take d)).1 ∧
    rowSlot pol phi s S (2*d+1) = (runRoles pol phi S ((path s).take d)).2 := by
  induction s generalizing S d with
  | stop a b =>
    have he : d = 0 := by simpa only [Spine.depth,Nat.le_zero] using hd
    subst d
    simp [path,runRoles]
  | step h i s ih =>
    cases d with
    | zero => simp [path,runRoles]
    | succ d =>
      have hds : d ≤ s.depth := by simp only [Spine.depth] at hd; omega
      have h0 : 2*(d+1) = 2*d+2 := by omega
      have h1 : 2*(d+1)+1 = (2*d+1)+2 := by omega
      simpa only [h0,h1,rowSlot_shift,path,List.take_succ_cons,runRoles] using ih (move pol phi S h i) d hds

def startFrame (Q : Query arity n) : Frame n :=
  ⟨false,initial pol Q.constraints false Q.left,initial pol Q.constraints true Q.right⟩

theorem physical_rows (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) :
    let F := runPhysical pol Q.constraints (startFrame pol Q) ((path s).take d)
    rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) (2*d) = (rolePair F).1 ∧
    rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) (2*d+1) = (rolePair F).2 := by
  dsimp only
  rw [run_rolePair]
  exact rowSlot_run pol Q.constraints s _ d hd

def roleOf (sign side : Bool) : Bool := if side then !sign else sign
def tokensOf (F : Frame n) (side : Bool) : Tokens n := if side then F.y else F.x

omit [DecidableEq H] in
/-- The role update is also the actual selected child pointer, not only
an isomorphism between the two token presentations. -/
theorem selected_role_pointer (h : H) (i : Fin (arity h)) (d : Nat) (r : Bool) :
    stepEmbed d (if r then MultiVarianceFlatStep.upperChild pol h i i
      else MultiVarianceFlatStep.lowerChild pol h i i) =
    shift d (if nextRole r (pol h i) then rootY d else rootX d) := by
  cases r <;> cases hp : pol h i <;>
    simp only [MultiVarianceFlatStep.upperChild,MultiVarianceFlatStep.lowerChild,ite_true,hp,
      nextRole,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
  all_goals apply Fin.ext; rfl

theorem frame_pick (F : Frame n) (side : Bool) :
    (if roleOf F.sign side then (rolePair F).2 else (rolePair F).1) = tokensOf F side := by
  cases hs : F.sign <;> cases side <;> simp [roleOf,tokensOf,rolePair,hs]

theorem physical_token_row (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (side : Bool) :
    let F := runPhysical pol Q.constraints (startFrame pol Q) ((path s).take d)
    rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right)
      (2*d+parity (roleOf F.sign side)) = tokensOf F side := by
  let F := runPhysical pol Q.constraints (startFrame pol Q) ((path s).take d)
  have hrows := physical_rows pol Q s d hd
  have hF := frame_pick F side
  change rowSlot pol Q.constraints s _ (2*d+parity (roleOf F.sign side)) = tokensOf F side
  cases hr : roleOf F.sign side <;> simp only [hr,parity,Bool.false_eq_true,if_false,if_true] at hF ⊢
  · simpa only [Nat.add_zero] using hrows.1.trans hF
  · exact hrows.2.trans hF

def railSlot (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) : Fin (width s.depth) :=
  ⟨2*d+parity r,by cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true,width] <;> omega⟩

omit [DecidableEq H] in
theorem railSlot_proper (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    (railSlot s d hd r).val < 2*s.depth+2 := by
  cases r <;> simp only [railSlot,parity,Bool.false_eq_true,if_false,if_true] <;> omega

omit [DecidableEq H] in
theorem railSlot_parity (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    (railSlot s d hd r).val%2 = parity r := by
  cases r <;> simp only [railSlot,parity,Bool.false_eq_true,if_false,if_true] <;> omega

/-- Exact original crossing on either physical rail at every level,
including the terminal level and coincident original query roots. -/
theorem physical_crossing_iff (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (side : Bool) (z : Fin n) :
    let F := runPhysical pol Q.constraints (startFrame pol Q) ((path s).take d)
    let r := roleOf F.sign side
    let p := slot Q.left Q.right s.depth (railSlot s d hd r)
    (if r then Support pol (extension pol Q s) (old s.depth z) p
      else Support pol (extension pol Q s) p (old s.depth z)) ↔ z ∈ tokensOf F side := by
  dsimp only
  rw [support_iff_row pol Q s _ (railSlot s d hd _) (railSlot_proper s d hd _) (railSlot_parity s d hd _)]
  change z ∈ rowSlot pol Q.constraints s _ (2*d+parity _) ↔ _
  rw [physical_token_row pol Q s d hd side]

end NSSE.MultiVarianceTokenExact
