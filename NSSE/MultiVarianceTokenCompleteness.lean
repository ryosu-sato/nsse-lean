import NSSE.MultiVarianceSpineRows

/-! An executable annotation invariant for every syntactic crossing.
It is exact on rail slots; shared fill slots remain an overapproximation
here and are never asserted to have exact token sets. -/
namespace NSSE.MultiVarianceTokenCompleteness
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceModelTokens (Tokens State)
open MultiVarianceSpineTokens MultiVarianceSpineSeparation MultiVarianceOriginalSpine
open MultiVarianceSpineCrossings MultiVarianceSpineRows MultiVarianceSpineNormal
open MultiVarianceSupportNormal
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem start_closed (Q : Query arity n) : StateClosed pol Q.constraints (start pol Q.constraints Q.left Q.right) :=
  ⟨initial_closed pol Q.constraints false Q.left,initial_closed pol Q.constraints true Q.right⟩

def annotation (Q : Query arity n) (s : Spine arity) (r : Bool) (k : Fin (count n s.depth)) : Tokens n :=
  if hk : k.val < n then initial pol Q.constraints r ⟨k.val,hk⟩
  else if (k.val-n)%2 = parity r then
    rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) (k.val-n+2)
  else ∅

@[simp] theorem annotation_old (Q : Query arity n) (s : Spine arity) (r : Bool) (x : Fin n) :
    annotation pol Q s r (old s.depth x) = initial pol Q.constraints r x := by
  simp only [annotation,old,x.isLt,dif_pos]

theorem annotation_slot (Q : Query arity n) (s : Spine arity) (r : Bool) (k : Fin (width s.depth))
    (hp : k.val%2 = parity r) :
    annotation pol Q s r (slot Q.left Q.right s.depth k) =
      rowSlot pol Q.constraints s (start pol Q.constraints Q.left Q.right) k.val := by
  by_cases h0 : k.val = 0
  · have he : k = rootX s.depth := Fin.ext h0
    subst k
    cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true,rootX,Fin.val_mk] at hp
    · change annotation pol Q s false (old s.depth Q.left) = rowSlot pol Q.constraints s _ 0
      rw [annotation_old,rowSlot_zero]
      rfl
    · omega
  by_cases h1 : k.val = 1
  · have he : k = rootY s.depth := Fin.ext h1
    subst k
    cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true,rootY,Fin.val_mk] at hp
    · omega
    · change annotation pol Q s true (old s.depth Q.right) = rowSlot pol Q.constraints s _ 1
      rw [annotation_old,rowSlot_one]
      rfl
  have hk : 2 ≤ k.val := by omega
  have hn : ¬n+(k.val-2)<n := by omega
  have hpar : (k.val-2)%2 = parity r := by omega
  simp [slot,h0,h1,annotation,hn,hpar,Nat.sub_add_cancel hk]

theorem annotation_closed (Q : Query arity n) (s : Spine arity) (r : Bool) (k : Fin (count n s.depth)) :
    Closed pol Q.constraints r (annotation pol Q s r k) := by
  unfold annotation
  split
  · exact initial_closed pol Q.constraints r _
  · split
    · apply rowSlot_closed pol Q.constraints s _ (start_closed pol Q) r
      omega
    · intro x hx
      exact False.elim (Finset.not_mem_empty _ hx)

theorem annotation_advances (Q : Query arity n) (s : Spine arity) :
    (∀ b ∈ (seeds pol Q s).lower, ∀ i,
      advance pol Q.constraints false (annotation pol Q s false b.parent) b.head i ⊆
      annotation pol Q s (nextRole false (pol b.head i)) (b.children i)) ∧
    (∀ b ∈ (seeds pol Q s).upper, ∀ i,
      advance pol Q.constraints true (annotation pol Q s true b.parent) b.head i ⊆
      annotation pol Q s (nextRole true (pol b.head i)) (b.children i)) := by
  constructor
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    intro i
    have hpar := (compile_parent_parity pol s).1 a ha
    have hchild := ((MultiVarianceSpineClasses.compile_shapes pol s).1 a ha i).2
    have hc : (a.children i).val%2 = parity (nextRole false (pol a.head i)) := by
      cases hn : pol a.head i <;> simpa only [hn,nextRole,parity,Bool.false_eq_true,
        Bool.not_false,if_false,if_true] using hchild
    dsimp only [mapBound]
    rw [annotation_slot pol Q s false a.parent hpar,annotation_slot pol Q s _ (a.children i) hc]
    exact (compile_advances pol Q.constraints s _).1 a ha i
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    intro i
    have hpar := (compile_parent_parity pol s).2 a ha
    have hchild := ((MultiVarianceSpineClasses.compile_shapes pol s).2 a ha i).2
    have hc : (a.children i).val%2 = parity (nextRole true (pol a.head i)) := by
      cases hn : pol a.head i <;> simpa only [hn,nextRole,parity,Bool.false_eq_true,
        Bool.not_true,if_false,if_true] using hchild
    dsimp only [mapBound]
    rw [annotation_slot pol Q s true a.parent hpar,annotation_slot pol Q s _ (a.children i) hc]
    exact (compile_advances pol Q.constraints s _).2 a ha i

theorem advance_child (phi : Constraints arity n) (r : Bool) (S : Tokens n)
    (h : H) (x : Fin n) (ds : Fin (arity h) → Fin n)
    (hm : (⟨x,h,ds⟩ : Bound arity n) ∈ (if r then phi.lower else phi.upper))
    (hx : x ∈ S) (i : Fin (arity h)) : ds i ∈ advance pol phi r S h i := by
  apply (mem_advance pol phi r S h i (ds i)).mpr
  refine ⟨x,ds,hm,hx,?_⟩
  cases nextRole r (pol h i) <;> exact Support.refl _

/-- All crossing derivations lie in the executable annotation. -/
theorem crossing_annotation (Q : Query arity n) (s : Spine arity) {r p z}
    (hc : Crossing pol Q.constraints (seeds pol Q s) (old s.depth) r p z) :
    z ∈ annotation pol Q s r p := by
  induction hc with
  | lowerRoot hs =>
    simpa only [annotation_old,initial,Bool.false_eq_true,if_false,MultiVarianceModelTokens.mem_up] using hs
  | upperRoot hs =>
    simpa only [annotation_old,initial,if_true,MultiVarianceModelTokens.mem_down] using hs
  | lowerClose _ hs ih => exact annotation_closed pol Q s false _ _ ih _ hs
  | upperClose hs _ ih => exact annotation_closed pol Q s true _ _ ih _ hs
  | @lowerCov h p cs x ds ha ho _ i hi ih =>
    have hm := advance_child pol Q.constraints false _ h x ds ho ih i
    have hout := (annotation_advances pol Q s).1 ⟨p,h,cs⟩ ha i hm
    simpa only [hi,nextRole,Bool.false_eq_true,if_false] using hout
  | @lowerCon h p cs x ds ha ho _ i hi ih =>
    have hm := advance_child pol Q.constraints false _ h x ds ho ih i
    have hout := (annotation_advances pol Q s).1 ⟨p,h,cs⟩ ha i hm
    simpa only [hi,nextRole,if_true,Bool.not_false] using hout
  | @upperCov h p cs x ds ho ha _ i hi ih =>
    have hm := advance_child pol Q.constraints true _ h x ds ho ih i
    have hout := (annotation_advances pol Q s).2 ⟨p,h,cs⟩ ha i hm
    simpa only [hi,nextRole,Bool.false_eq_true,if_false] using hout
  | @upperCon h p cs x ds ho ha _ i hi ih =>
    have hm := advance_child pol Q.constraints true _ h x ds ho ih i
    have hout := (annotation_advances pol Q s).2 ⟨p,h,cs⟩ ha i hm
    simpa only [hi,nextRole,if_true,Bool.not_true] using hout

end NSSE.MultiVarianceTokenCompleteness
