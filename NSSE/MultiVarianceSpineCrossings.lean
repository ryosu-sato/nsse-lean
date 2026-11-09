import NSSE.MultiVarianceSpineTokens

/-! Every computed token is supported in the actual single global spine
extension.  The proof includes both signed decomposition rules and never
identifies a physical rail with a fixed lower/upper role. -/
namespace NSSE.MultiVarianceSpineCrossings
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceModelTokens (Tokens State)
open MultiVarianceSpineTokens MultiVarianceSpineSeparation MultiVarianceOriginalSpine
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n m : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)
variable (theta : Constraints arity m) (oldMap : Fin n → Fin m)

def Crosses (upper : Bool) (p : Fin m) (S : Tokens n) : Prop :=
  ∀ v ∈ S, if upper then Support pol theta (oldMap v) p else Support pol theta p (oldMap v)

variable (hl : ∀ a ∈ phi.lower, mapBound oldMap a ∈ theta.lower)
variable (hu : ∀ a ∈ phi.upper, mapBound oldMap a ∈ theta.upper)

include hl hu in
theorem crossing_advance (r : Bool) (S : Tokens n) (h : H) (p : Fin m)
    (cs : Fin (arity h) → Fin m)
    (hb : if r then (⟨p,h,cs⟩ : Bound arity m) ∈ theta.upper else ⟨p,h,cs⟩ ∈ theta.lower)
    (hc : Crosses pol theta oldMap r p S) (i : Fin (arity h)) :
    Crosses pol theta oldMap (nextRole r (pol h i)) (cs i) (advance pol phi r S h i) := by
  intro v hv
  obtain ⟨q,ds,hmem,hq,hs⟩ := (mem_advance pol phi r S h i v).mp hv
  have hp := hc q hq
  have lift : ∀ {x y}, Support pol phi x y → Support pol theta (oldMap x) (oldMap y) :=
    fun hs => MultiVarianceSupportClasses.lift_support pol phi oldMap theta hl hu hs
  cases r <;> cases hn : pol h i <;>
    simp only [hn,nextRole,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      if_false,if_true] at hb hmem hs hp ⊢
  · have hd := Support.decompCov (a := cs) (b := fun j => oldMap (ds j)) hb (hu _ hmem) hp i hn
    exact hd.trans (lift hs)
  · have hd := Support.decompCon (a := cs) (b := fun j => oldMap (ds j)) hb (hu _ hmem) hp i hn
    exact (lift hs).trans hd
  · have hd := Support.decompCov (a := fun j => oldMap (ds j)) (b := cs) (hl _ hmem) hb hp i hn
    exact (lift hs).trans hd
  · have hd := Support.decompCon (a := fun j => oldMap (ds j)) (b := cs) (hl _ hmem) hb hp i hn
    exact hd.trans (lift hs)

include hl hu in
theorem initial_crosses (r : Bool) (x : Fin n) :
    Crosses pol theta oldMap r (oldMap x) (initial pol phi r x) := by
  intro v hv
  have lift : ∀ {x y}, Support pol phi x y → Support pol theta (oldMap x) (oldMap y) :=
    fun hs => MultiVarianceSupportClasses.lift_support pol phi oldMap theta hl hu hs
  cases r <;> simp only [initial,Bool.false_eq_true,if_false,if_true,
    MultiVarianceModelTokens.mem_up,MultiVarianceModelTokens.mem_down] at hv ⊢
  all_goals exact lift hv

/-- The recursive predicate records every proper and terminal level. -/
def AllCrossings : (s : Spine arity) → (Fin (width s.depth) → Fin m) → State n → Prop
  | .stop _ _, f, S =>
      Crosses pol theta oldMap false (f (rootX 0)) S.1 ∧
      Crosses pol theta oldMap true (f (rootY 0)) S.2
  | .step h i s, f, S =>
      (Crosses pol theta oldMap false (f (rootX (s.depth+1))) S.1 ∧
       Crosses pol theta oldMap true (f (rootY (s.depth+1))) S.2) ∧
      AllCrossings s (fun k => f (shift s.depth k)) (move pol phi S h i)

include hl hu in
theorem all_crossings (s : Spine arity) (f : Fin (width s.depth) → Fin m) (S : State n)
    (hlo : ∀ b ∈ (compile pol s).lower, mapBound f b ∈ theta.lower)
    (hup : ∀ b ∈ (compile pol s).upper, mapBound f b ∈ theta.upper)
    (hX : Crosses pol theta oldMap false (f (rootX s.depth)) S.1)
    (hY : Crosses pol theta oldMap true (f (rootY s.depth)) S.2) :
    AllCrossings pol phi theta oldMap s f S := by
  induction s generalizing S with
  | stop a b => exact ⟨hX,hY⟩
  | step h i s ih =>
    refine ⟨⟨hX,hY⟩,?_⟩
    have hlb : (⟨f (rootX (s.depth+1)),h,
        fun j => f (stepEmbed s.depth (MultiVarianceFlatStep.lowerChild pol h i j))⟩ : Bound arity m) ∈ theta.lower :=
      hlo (mapBound (stepEmbed s.depth) ⟨0,h,MultiVarianceFlatStep.lowerChild pol h i⟩)
        (List.mem_append_left _ (List.mem_map.mpr ⟨_,List.mem_singleton.mpr rfl,rfl⟩))
    have hub : (⟨f (rootY (s.depth+1)),h,
        fun j => f (stepEmbed s.depth (MultiVarianceFlatStep.upperChild pol h i j))⟩ : Bound arity m) ∈ theta.upper :=
      hup (mapBound (stepEmbed s.depth) ⟨1,h,MultiVarianceFlatStep.upperChild pol h i⟩)
        (List.mem_append_left _ (List.mem_map.mpr ⟨_,List.mem_singleton.mpr rfl,rfl⟩))
    have hL := crossing_advance pol phi theta oldMap hl hu false S.1 h _ _ hlb hX i
    have hR := crossing_advance pol phi theta oldMap hl hu true S.2 h _ _ hub hY i
    apply ih
    · intro b hb
      exact hlo (mapBound (shift s.depth) b)
        (List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
    · intro b hb
      exact hup (mapBound (shift s.depth) b)
        (List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
    · cases hn : pol h i <;>
        simp only [move,hn,nextRole,Bool.false_eq_true,if_false,if_true,
          Bool.not_true,Bool.not_false,MultiVarianceFlatStep.lowerChild,
          MultiVarianceFlatStep.upperChild,ite_true] at hL hR ⊢
      · exact hL
      · exact hR
    · cases hn : pol h i <;>
        simp only [move,hn,nextRole,Bool.false_eq_true,if_false,if_true,
          Bool.not_true,Bool.not_false,MultiVarianceFlatStep.lowerChild,
          MultiVarianceFlatStep.upperChild,ite_true] at hL hR ⊢
      · exact hR
      · exact hL

def start (x y : Fin n) : State n := (initial pol phi false x,initial pol phi true y)

theorem extension_crossings (Q : Query arity n) (s : Spine arity) :
    AllCrossings pol Q.constraints (extension pol Q s) (old s.depth) s
      (slot Q.left Q.right s.depth) (start pol Q.constraints Q.left Q.right) := by
  have hl : ∀ a ∈ Q.constraints.lower, mapBound (old s.depth) a ∈ (extension pol Q s).lower := by
    intro a ha
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hu : ∀ a ∈ Q.constraints.upper, mapBound (old s.depth) a ∈ (extension pol Q s).upper := by
    intro a ha
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  apply all_crossings pol Q.constraints (extension pol Q s) (old s.depth) hl hu
  · intro b hb
    exact List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
  · intro b hb
    exact List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
  · exact initial_crosses pol Q.constraints (extension pol Q s) (old s.depth) hl hu false Q.left
  · exact initial_crosses pol Q.constraints (extension pol Q s) (old s.depth) hl hu true Q.right

omit [DecidableEq H] in
theorem birth_support (r t : Bool) (p q : Fin m) (S T : Tokens n)
    (hS : Crosses pol theta oldMap r p S) (hT : Crosses pol theta oldMap t q T)
    (hb : Birth pol phi r S t T)
    (lift : ∀ {x y}, Support pol phi x y → Support pol theta (oldMap x) (oldMap y)) :
    Support pol theta p q := by
  obtain ⟨rfl,rfl,u,hu,v,hv,hs⟩ := hb
  exact (hS u hu).trans ((lift hs).trans (hT v hv))

end NSSE.MultiVarianceSpineCrossings
