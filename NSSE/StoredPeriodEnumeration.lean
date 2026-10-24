import NSSE.StoredPeriodWords

namespace NSSE.StoredPeriodEnumeration
variable {α β : Type} {p : Nat}

def pack : (ws : List (List α)) → (∀ w ∈ ws, w.length ≤ p) → List (BoundedWord α p) × Nat
  | [],_ => ([],1)
  | w::ws,h => let t := pack ws (fun a ha => h a (List.mem_cons_of_mem _ ha))
               (⟨w,h w (by simp)⟩::t.1,1+t.2)

theorem pack_words (ws : List (List α)) (h : ∀ w ∈ ws, w.length ≤ p) :
    (pack ws h).1.map BoundedWord.word = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [pack,List.map_cons,ih]

theorem pack_cost (ws : List (List α)) (h : ∀ w ∈ ws, w.length ≤ p) :
    (pack ws h).2 = ws.length+1 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [pack,ih,List.length_cons]; omega

theorem pack_value (alphabet : Enumeration α) (h : ∀ w ∈ wordsUpTo alphabet p, w.length ≤ p) :
    (pack (wordsUpTo alphabet p) h).1 = (boundedWordEnumeration alphabet p).values := by
  apply (List.map_injective_iff (f := BoundedWord.word)).mpr (by
    intro a b he; cases a; cases b; cases he; rfl)
  rw [pack_words]
  simp [boundedWordEnumeration,List.map_map]

def cross (xs : List α) (ys : List β) : List (α × β) × Nat :=
  CountedListConstruction.flatMap (fun x => CountedListConstruction.map (fun y => ((x,y),1)) ys) xs

theorem cross_value (xs : List α) (ys : List β) :
    (cross xs ys).1 = xs.flatMap (fun x => ys.map (fun y => (x,y))) := by
  simp only [cross,CountedListConstruction.flatMap_value,CountedListConstruction.map_value]

theorem cross_length (xs : List α) (ys : List β) : (cross xs ys).1.length = xs.length*ys.length := by
  simp [cross_value,List.length_flatMap,List.map_const',List.sum_replicate,smul_eq_mul]

def crossBudget (n m : Nat) := 1+n*(3+3*m)

theorem cross_bound (xs : List α) (ys : List β) : (cross xs ys).2 ≤ crossBudget xs.length ys.length := by
  have hm (x : α) := CountedListConstruction.map_bound (fun y : β => ((x,y),1)) ys 1 (fun _ _ => le_rfl)
  have h := CountedListConstruction.flatMap_bound
    (fun x => CountedListConstruction.map (fun y : β => ((x,y),1)) ys) xs
    (1+2*ys.length) ys.length (fun x _ => by simpa only [Nat.mul_comm] using hm x)
    (fun _ _ => by simp only [CountedListConstruction.map_value,List.length_map]; exact le_rfl)
  dsimp only [crossBudget,cross]
  nlinarith

theorem finValues_eq (n : Nat) : finValues n = List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finValues,List.finRange_succ_eq_map,ih]

def alphabet (d : Nat) : Enumeration (Fin d) where
  values := (CountedFinEnumeration.enumerate d).1
  complete := by intro i; rw [CountedFinEnumeration.value]; exact List.mem_finRange i

theorem alphabet_value (d : Nat) : alphabet d = finEnumeration d := by
  unfold alphabet finEnumeration
  simp only [CountedFinEnumeration.value,finValues_eq]

def buffers (letters : Enumeration α) (p : Nat) : List (BoundedWord α p) × Nat :=
  let w := StoredPeriodWords.upTo letters p
  let b := pack w.1 (by
    intro x hx; rw [StoredPeriodWords.upTo_value] at hx
    exact (mem_wordsUpTo_iff _ _ _).mp hx)
  (b.1,1+w.2+b.2)

theorem buffers_value (letters : Enumeration α) (p : Nat) :
    (buffers letters p).1 = (boundedWordEnumeration letters p).values := by
  simp only [buffers,StoredPeriodWords.upTo_value,pack_value]

theorem buffers_bound (letters : Enumeration α) (p : Nat) :
    (buffers letters p).2 ≤
      2+StoredPeriodWords.upToBudget letters.values.length p+(wordsUpTo letters p).length := by
  have h := StoredPeriodWords.upTo_bound letters p
  simp only [buffers,pack_cost,StoredPeriodWords.upTo_value]
  omega

/-- The actual list order is the order used by the original monitor encoder. -/
def build (d n p : Nat) : List (PeriodMonitorState (Fin d) (Fin n) p) × Nat :=
  let a := CountedFinEnumeration.enumerate d
  let letters : Enumeration (Fin d) := ⟨a.1,(alphabet d).complete⟩
  let b := buffers letters p
  let q := CountedFinEnumeration.enumerate n
  let o := CountedFinEnumeration.enumerate p
  let x := cross b.1 q.1
  let y := cross x.1 o.1
  let z := cross y.1 [false,true]
  let t := cross z.1 [false,true]
  let r := CountedListConstruction.map (fun v =>
    (⟨v.1.1.1.1,v.1.1.1.2,v.1.1.2,v.1.2,v.2⟩,1)) t.1
  (r.1,4+a.2+b.2+q.2+o.2+x.2+y.2+z.2+t.2+r.2)

theorem value (d n p : Nat) : (build d n p).1 =
    (periodMonitorStateEnumeration (finEnumeration d) (finEnumeration n) p).values := by
  simp only [build,CountedListConstruction.map_value,buffers_value]
  simp only [show (⟨(CountedFinEnumeration.enumerate d).1,(alphabet d).complete⟩ : Enumeration (Fin d)) =
    finEnumeration d from alphabet_value d,CountedFinEnumeration.value,cross_value]
  simp only [periodMonitorStateEnumeration,Enumeration.mapOnto,Enumeration.product,
    finEnumeration,finValues_eq,periodMonitorBoolEnumeration]

def budget (d n p W : Nat) :=
  4+(d+1)^2+(2+StoredPeriodWords.upToBudget d p+W)+(n+1)^2+(p+1)^2+
    crossBudget W n+crossBudget (W*n) p+crossBudget (W*n*p) 2+
    crossBudget (W*n*p*2) 2+(1+2*(W*n*p*4))

theorem bound (d n p : Nat) : (build d n p).2 ≤
    budget d n p (wordsUpTo (finEnumeration d) p).length := by
  let b := buffers (alphabet d) p
  let q := CountedFinEnumeration.enumerate n
  let o := CountedFinEnumeration.enumerate p
  let x := cross b.1 q.1
  let y := cross x.1 o.1
  let z := cross y.1 [false,true]
  let t := cross z.1 [false,true]
  let W := (wordsUpTo (finEnumeration d) p).length
  have hb : b.2 ≤ 2+StoredPeriodWords.upToBudget d p+W := by
    have h := buffers_bound (alphabet d) p
    simpa only [b,W,alphabet_value,finEnumeration,ExplicitPeriodMonitorSize.finValues_length] using h
  have hbl : b.1.length = W := by
    simp only [b,buffers_value,alphabet_value,boundedWordEnumeration,List.length_map,List.length_attach,W]
  have hq : q.1.length=n := by simp only [q,CountedFinEnumeration.value,List.length_finRange]
  have ho : o.1.length=p := by simp only [o,CountedFinEnumeration.value,List.length_finRange]
  have hx := cross_bound b.1 q.1
  have hy := cross_bound x.1 o.1
  have hz := cross_bound y.1 [false,true]
  have ht := cross_bound z.1 [false,true]
  have hlx : x.1.length=W*n := by simp only [x,cross_length,hbl,hq]
  have hly : y.1.length=W*n*p := by simp only [y,cross_length,hlx,ho]
  have hlz : z.1.length=W*n*p*2 := by simp only [z,cross_length,hly,List.length_cons,List.length_nil]
  have hlt : t.1.length=W*n*p*4 := by simp only [t,cross_length,hlz,List.length_cons,List.length_nil]; ring
  have hr := CountedListConstruction.map_bound
    (fun v : (((BoundedWord (Fin d) p × Fin n) × Fin p) × Bool) × Bool =>
      ((⟨v.1.1.1.1,v.1.1.1.2,v.1.1.2,v.1.2,v.2⟩ : PeriodMonitorState (Fin d) (Fin n) p),1))
    t.1 1 (fun _ _ => le_rfl)
  simp only [hbl,hq,ho,hlx,hly,hlz,hlt,List.length_cons,List.length_nil] at hx hy hz ht hr
  have ha := CountedFinEnumeration.bound d
  have hqc := CountedFinEnumeration.bound n
  have hoc := CountedFinEnumeration.bound p
  change 4+_+b.2+q.2+o.2+x.2+y.2+z.2+t.2+_ ≤ _
  unfold budget
  dsimp only [b,q,o,x,y,z,t,W,alphabet] at *
  norm_num only at hx hy hz ht hr
  omega

theorem bound_explicit (d n p : Nat) : (build d n p).2 ≤
    budget d n p ((p+1)*(d+1)^p) := by
  apply (bound d n p).trans
  have hw := ExplicitPeriodMonitorSize.wordsUpTo_bound (finEnumeration d) p
  simp only [finEnumeration,ExplicitPeriodMonitorSize.finValues_length] at hw
  unfold budget crossBudget
  gcongr <;> exact hw

theorem length (d n p : Nat) : (build d n p).1.length =
    (wordsUpTo (finEnumeration d) p).length*n*p*4 := by
  rw [value]
  simp only [periodMonitorStateEnumeration,Enumeration.mapOnto,List.length_map]
  rw [ExplicitPeriodMonitorSize.product_length,ExplicitPeriodMonitorSize.product_length,
    ExplicitPeriodMonitorSize.product_length,ExplicitPeriodMonitorSize.product_length]
  simp only [boundedWordEnumeration,List.length_map,List.length_attach,finEnumeration,
    ExplicitPeriodMonitorSize.finValues_length,periodMonitorBoolEnumeration,List.length_cons,List.length_nil]
  ring
end NSSE.StoredPeriodEnumeration
