import NSSE.MultiVarianceRailBirths

/-! Actual literal origins of the recursive signed spine compiler.
Every added constructor literal comes from one suffix root. -/
namespace NSSE.MultiVarianceSpineSuffixes
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceTokenExact
variable {H : Type*} {arity : H → Nat}

def suffix (s : Spine arity) (d : Nat) : Spine arity := match d with
  | 0 => s
  | k+1 => match s with
    | .stop a b => .stop a b
    | .step _ _ t => suffix t k
termination_by structural d

theorem suffix_depth (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) :
    (suffix s d).depth+d = s.depth := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    cases s with
    | stop a b => simp only [Spine.depth] at hd; omega
    | step h i s =>
      have hd' : d ≤ s.depth := by simp only [Spine.depth] at hd; omega
      have he := ih s hd'
      simpa only [suffix,Spine.depth,Nat.add_assoc] using congrArg (fun k => k+1) he

theorem suffix_path (s : Spine arity) (d : Nat) : path (suffix s d) = (path s).drop d := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => cases s <;> simp only [suffix,path,List.drop_nil,List.drop_succ_cons,ih]

def embed (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) :
    Fin (width (suffix s d).depth) → Fin (width s.depth) :=
  fun k => ⟨2*d+k.val,by have hk := k.isLt; have he := suffix_depth s d hd; simp only [width] at hk ⊢; omega⟩

@[simp] theorem embed_zero (s : Spine arity) (k : Fin (width s.depth)) :
    embed s 0 (Nat.zero_le _) k = k := by apply Fin.ext; simp [embed]

theorem embed_succ (h : H) (i : Fin (arity h)) (s : Spine arity) (d : Nat)
    (hd : d+1 ≤ (Spine.step h i s).depth) (ht : d ≤ s.depth)
    (k : Fin (width (suffix s d).depth)) :
    embed (.step h i s) (d+1) hd k = shift s.depth (embed s d ht k) := by
  apply Fin.ext
  dsimp only [embed,shift]
  omega

@[simp] theorem mapBound_id {m : Nat} (b : Bound arity m) : mapBound id b = b := by cases b; rfl

theorem mapBound_comp {l m n : Nat} (f : Fin l → Fin m) (g : Fin m → Fin n) (b : Bound arity l) :
    mapBound (fun x => g (f x)) b = mapBound g (mapBound f b) := rfl

def bounds {n : Nat} (phi : Constraints arity n) (upper : Bool) : List (Bound arity n) :=
  if upper then phi.upper else phi.lower

@[simp] theorem bounds_combine {n : Nat} (a b : Constraints arity n) (r : Bool) :
    bounds (combine a b) r = bounds a r ++ bounds b r := by cases r <;> rfl

@[simp] theorem bounds_remap {m n : Nat} (f : Fin m → Fin n) (phi : Constraints arity m) (r : Bool) :
    bounds (remap f phi) r = (bounds phi r).map (mapBound f) := by cases r <;> rfl

variable (pol : Polarity arity)

def rootBounds : (s : Spine arity) → Bool → List (Bound arity (width s.depth))
  | .stop a b, r => bounds (MultiVarianceFlatStop.stopConstraints pol a b) r
  | .step h i s, r => bounds (remap (stepEmbed s.depth) (MultiVarianceFlatStep.stepConstraints pol h i)) r

theorem compile_step_bounds (h : H) (i : Fin (arity h)) (s : Spine arity) (r : Bool) :
    bounds (compile pol (.step h i s)) r =
      List.append (rootBounds pol (.step h i s) r) ((bounds (compile pol s) r).map (mapBound (shift s.depth))) := by
  cases r <;> rfl

theorem root_mem (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b ∈ rootBounds pol s r) : b ∈ bounds (compile pol s) r := by
  cases s with
  | stop a c => exact hb
  | step h i s => rw [compile_step_bounds]; exact List.mem_append_left _ hb

theorem suffix_mem (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool)
    (b : Bound arity (width (suffix s d).depth)) (hb : b ∈ bounds (compile pol (suffix s d)) r) :
    mapBound (embed s d hd) b ∈ bounds (compile pol s) r := by
  induction d generalizing s with
  | zero =>
    have he : embed s 0 hd = id := funext (embed_zero s)
    rw [he,mapBound_id]
    exact hb
  | succ d ih =>
    cases s with
    | stop a c => simp only [Spine.depth] at hd; omega
    | step h i s =>
      have ht : d ≤ s.depth := by simp only [Spine.depth] at hd; omega
      have he : embed (.step h i s) (d+1) hd = fun k => shift s.depth (embed s d ht k) :=
        funext (embed_succ h i s d hd ht)
      rw [he,mapBound_comp (embed s d ht) (shift s.depth) b,compile_step_bounds]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih s ht b hb,rfl⟩)

theorem suffix_root_mem (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool)
    (b : Bound arity (width (suffix s d).depth)) (hb : b ∈ rootBounds pol (suffix s d) r) :
    mapBound (embed s d hd) b ∈ bounds (compile pol s) r :=
  suffix_mem pol s d hd r b (root_mem pol (suffix s d) r b hb)

/-- Exhaustive origins, including terminal heads and repeated root aliases
after the caller applies the original-variable remapping. -/
theorem bound_origin (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b ∈ bounds (compile pol s) r) :
    ∃ d, ∃ hd : d ≤ s.depth, ∃ c : Bound arity (width (suffix s d).depth),
      c ∈ rootBounds pol (suffix s d) r ∧ b = mapBound (embed s d hd) c := by
  induction s with
  | stop a c =>
    refine ⟨0,Nat.zero_le _,b,hb,?_⟩
    have he : embed (arity := arity) (.stop a c) 0 (Nat.zero_le _) = id :=
      funext (embed_zero (.stop a c : Spine arity))
    rw [he,mapBound_id]
  | step h i s ih =>
    rw [compile_step_bounds] at hb
    rcases List.mem_append.mp hb with hb | hb
    · refine ⟨0,Nat.zero_le _,b,hb,?_⟩
      have he : embed (.step h i s) 0 (Nat.zero_le _) = id := funext (embed_zero _)
      rw [he,mapBound_id]
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      obtain ⟨d,hd,a,ha,he⟩ := ih c hc
      have ht : d+1 ≤ (Spine.step h i s).depth := by simp only [Spine.depth]; omega
      refine ⟨d+1,ht,a,ha,?_⟩
      have hf : embed (.step h i s) (d+1) ht = fun k => shift s.depth (embed s d hd k) :=
        funext (embed_succ h i s d ht hd)
      rw [hf,mapBound_comp (embed s d hd) (shift s.depth) a,he]

theorem mem_iff_origin (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth)) :
    b ∈ bounds (compile pol s) r ↔
      ∃ d, ∃ hd : d ≤ s.depth, ∃ c : Bound arity (width (suffix s d).depth),
        c ∈ rootBounds pol (suffix s d) r ∧ b = mapBound (embed s d hd) c := by
  constructor
  · exact bound_origin pol s r b
  · rintro ⟨d,hd,c,hc,rfl⟩
    exact suffix_root_mem pol s d hd r c hc

end NSSE.MultiVarianceSpineSuffixes
