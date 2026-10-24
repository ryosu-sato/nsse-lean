import NSSE.ContraSoundness

/-! # The terminal gadget `Θ = Ψ(N,N)` of a contravariant query and a word (stage S4, part 1)

notes_v1364 §1 (setting, the gadget), §5 Lemma E; v1361 §7.

Fix a four-form system `φ` over `Fin n`, the query `x ≤ y`, a word `w` (`N = |w|`) and a side.
The gadget adds fresh variables `B_` (`bt`, with `bot`), `T_` (`tt`, with `top`) and the rail
tokens `X_1..X_N`, `Y_1..Y_N` (`rail false k`, `rail true k` stand for level `k+1`); level `0` of
the x-rail is `x`, of the y-rail is `y`. A POSITION is a rail `r` (`false = X`, `true = Y`) and a
level `k ≤ N`; its token is `tokP r k`.

The literals are described uniformly, which is v1364 §1 read through the class table of
Lemma A.0: a position `(r,k)` is an OUT-position iff `pol(w[:k]) = r` (`X` at `+`, `Y` at `−`),
otherwise an IN-position. Every position except the LEAF position `(leaf, N)` (`leaf = Y` on the
right side, `X` on the left side) carries one rail literal: a LOWER literal `f(c̄) ≤ tok` at an
out-position and an UPPER literal `tok ≤ f(c̄)` at an in-position. Its children are the next
rail token at the letter `w[k]` (when `k < N`) and the FILLS elsewhere: `B_`/`T_` at a
covariant/contravariant position of a lower literal, `T_`/`B_` of an upper literal. The leaf
position carries `top` if it is an out-position and `bot` if it is an in-position.
On the right side this is exactly v1364 §1 (x-rail lower at `+`, upper at `−`; y-rail the
opposite; `f(fills) ≤ X_N` / `X_N ≤ f(fills)` by `pol(w)`; `bot(Y_N)` / `top(Y_N)` by `pol(w)`), and
on the left side its mirror.

The gadget is an actual `Constraints (n + 2 + 2N) d` extending `φ` (the original variables are
`Fin.castAdd`-embedded; `theta_satisfies_restrict`). Tokens are decoded by `Setup.dec`.

**Lemma E** (`failure`): every solution of `Θ` realises the failure of `w` on the side. The proof is
the rail induction of v1364 §5 with one signed quantity per rail: `val r k = plabel_{μ}(ρ(tok r k),
w[k:])` with `μ = pol(w[:k]) xor r` decreases weakly along every rail; the leaf position has value
`2` and the other end has value `≥ 1`.
-/

namespace NSSE.ContraGadget

open SubtypeConstraints (Constraints Query BoundLiteral)
open AbsorbingSubtypeTrees
open ContraTrees ContraConstraints ContraSupport ContraClashes ContraAutomaton ContraSoundness
open ForwardTableAutomaton (Side)

variable {n d : Nat}

/-! ## Tokens and their encoding as variables -/

/-- Variables of the gadget: original ones, the two fills, and the rail tokens (`rail r k` is
the token at level `k+1` of rail `r`). -/
inductive Tok (n N : Nat) where
  | orig (v : Fin n)
  | bt
  | tt
  | rail (r : Bool) (k : Fin N)
  deriving DecidableEq

/-- Number of gadget variables. -/
def size (n N : Nat) : Nat := n + 2 + 2 * N

def enc {N : Nat} : Tok n N → Fin (size n N)
  | .orig v => ⟨v.1, by unfold size; omega⟩
  | .bt => ⟨n, by unfold size; omega⟩
  | .tt => ⟨n + 1, by unfold size; omega⟩
  | .rail false k => ⟨n + 2 + k.1, by unfold size; omega⟩
  | .rail true k => ⟨n + 2 + N + k.1, by unfold size; omega⟩

def dec {N : Nat} (a : Fin (size n N)) : Tok n N :=
  if h : a.1 < n then .orig ⟨a.1, h⟩
  else if h1 : a.1 = n then .bt
  else if h1' : a.1 = n + 1 then .tt
  else if h2 : a.1 - (n + 2) < N then .rail false ⟨a.1 - (n + 2), h2⟩
  else .rail true ⟨a.1 - (n + 2) - N, by have := a.2; unfold size at this; omega⟩

@[simp] theorem dec_enc {N : Nat} (t : Tok n N) : dec (enc t) = t := by
  rcases t with v | _ | _ | ⟨r, k⟩
  · simp [enc, dec]
  · simp [enc, dec]
  · simp [enc, dec]
  · have hk := k.2
    cases r
    · simp only [enc, dec]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      congr 1; ext; simp
    · simp only [enc, dec]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      congr 1; ext; simp; omega

theorem enc_dec {N : Nat} (a : Fin (size n N)) : enc (dec a) = a := by
  have := a.2; unfold size at this
  unfold dec
  split_ifs <;> apply Fin.ext <;> simp [enc] <;> omega

theorem dec_injective {N : Nat} : Function.Injective (dec : Fin (size n N) → Tok n N) :=
  fun a b h => by rw [← enc_dec a, h, enc_dec]

theorem enc_injective {N : Nat} : Function.Injective (enc : Tok n N → Fin (size n N)) :=
  fun a b h => by rw [← dec_enc a, h, dec_enc]

/-- An original literal read on tokens. -/
def origLit {N : Nat} (a : BoundLiteral n d) : Tok n N × (Fin d → Tok n N) :=
  (.orig a.1, fun i => .orig (a.2 i))

def encLit {N : Nat} (l : Tok n N × (Fin d → Tok n N)) : BoundLiteral (size n N) d :=
  (enc l.1, fun i => enc (l.2 i))

/-! ## The data of a gadget -/

/-- The rail ending in a leaf: `Y` on the right side, `X` on the left side. -/
def leafRail : Side → Bool
  | .left => false
  | .right => true

theorem tracked_eq (side : Side) (q : Triple n) :
    tracked side q = if leafRail side then q.2.1 else q.1 := by
  cases side <;> rfl

structure Setup (n d : Nat) where
  POL : Polarity d
  φ : Constraints n d
  x : Fin n
  y : Fin n
  w : List (Fin d)
  side : Side

namespace Setup

variable (g : Setup n d)

abbrev N : Nat := g.w.length

def leaf : Bool := leafRail g.side

/-- `pol(w[:k])`. -/
def sig (k : Nat) : Bool := pathPol g.POL (g.w.take k)

/-- Out-position: `pol(w[:k]) = r`. -/
def out (r : Bool) (k : Nat) : Bool := g.sig k == r

/-- The position carries a rail literal (every position except the leaf position). -/
def hasLit (r : Bool) (k : Nat) : Bool := decide (k < g.N) || (r != g.leaf)

/-- The token at a position. -/
def tokP (r : Bool) (k : Nat) : Tok n g.N :=
  if k = 0 then .orig (if r then g.y else g.x)
  else if h : k - 1 < g.N then .rail r ⟨k - 1, h⟩ else .bt

/-- The fills of a lower (`low = true`) resp. upper literal. -/
def fill (low : Bool) (j : Fin d) : Tok n g.N :=
  if low then (if g.POL j then .tt else .bt) else (if g.POL j then .bt else .tt)

/-- The children of the rail literal at `(r,k)`. -/
def children (r : Bool) (k : Nat) : Fin d → Tok n g.N := fun j =>
  if g.w[k]? = some j then g.tokP r (k + 1) else g.fill (g.out r k) j

def railLit (p : Bool × Nat) : Tok n g.N × (Fin d → Tok n g.N) :=
  (g.tokP p.1 p.2, g.children p.1 p.2)

def positions : List (Bool × Nat) :=
  (List.range (g.N + 1)).flatMap (fun k => [(false, k), (true, k)])

theorem mem_positions (p : Bool × Nat) : p ∈ g.positions ↔ p.2 ≤ g.N := by
  rcases p with ⟨r, k⟩
  cases r <;> simp [positions, Nat.lt_succ_iff]

def tokLower : List (Tok n g.N × (Fin d → Tok n g.N)) :=
  g.φ.lower.map origLit ++
    (g.positions.filter (fun p => g.out p.1 p.2 && g.hasLit p.1 p.2)).map g.railLit

def tokUpper : List (Tok n g.N × (Fin d → Tok n g.N)) :=
  g.φ.upper.map origLit ++
    (g.positions.filter (fun p => !g.out p.1 p.2 && g.hasLit p.1 p.2)).map g.railLit

def tokBot : List (Tok n g.N) :=
  g.φ.bot.map .orig ++ .bt :: (if g.out g.leaf g.N then [] else [g.tokP g.leaf g.N])

def tokTop : List (Tok n g.N) :=
  g.φ.top.map .orig ++ .tt :: (if g.out g.leaf g.N then [g.tokP g.leaf g.N] else [])

/-- **The terminal gadget** `Θ`, as an actual four-form system over `size n N` variables. -/
def theta : Constraints (size n g.N) d where
  upper := g.tokUpper.map encLit
  lower := g.tokLower.map encLit
  bot := g.tokBot.map enc
  top := g.tokTop.map enc

/-! ### Membership -/

theorem mem_tokLower (l : Tok n g.N × (Fin d → Tok n g.N)) : l ∈ g.tokLower ↔
    (∃ a ∈ g.φ.lower, l = origLit a) ∨
    ∃ r k, k ≤ g.N ∧ g.out r k = true ∧ g.hasLit r k = true ∧ l = (g.tokP r k, g.children r k) := by
  simp only [tokLower, List.mem_append, List.mem_map, List.mem_filter, mem_positions,
    Bool.and_eq_true]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨⟨r, k⟩, ⟨hk, ho, hl⟩, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨r, k, hk, ho, hl, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨r, k, hk, ho, hl, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨(r, k), ⟨hk, ho, hl⟩, rfl⟩

theorem mem_tokUpper (l : Tok n g.N × (Fin d → Tok n g.N)) : l ∈ g.tokUpper ↔
    (∃ a ∈ g.φ.upper, l = origLit a) ∨
    ∃ r k, k ≤ g.N ∧ g.out r k = false ∧ g.hasLit r k = true ∧ l = (g.tokP r k, g.children r k) := by
  simp only [tokUpper, List.mem_append, List.mem_map, List.mem_filter, mem_positions,
    Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨⟨r, k⟩, ⟨hk, ho, hl⟩, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨r, k, hk, ho, hl, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨r, k, hk, ho, hl, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨(r, k), ⟨hk, ho, hl⟩, rfl⟩

theorem mem_tokBot (t : Tok n g.N) : t ∈ g.tokBot ↔
    (∃ v ∈ g.φ.bot, t = .orig v) ∨ t = .bt ∨ (g.out g.leaf g.N = false ∧ t = g.tokP g.leaf g.N) := by
  unfold tokBot
  cases h : g.out g.leaf g.N <;> simp [eq_comm]

theorem mem_tokTop (t : Tok n g.N) : t ∈ g.tokTop ↔
    (∃ v ∈ g.φ.top, t = .orig v) ∨ t = .tt ∨ (g.out g.leaf g.N = true ∧ t = g.tokP g.leaf g.N) := by
  unfold tokTop
  cases h : g.out g.leaf g.N <;> simp [eq_comm]

theorem mem_theta_lower {a : BoundLiteral (size n g.N) d} : a ∈ g.theta.lower ↔
    ∃ l ∈ g.tokLower, a = encLit l := by
  simp [theta, eq_comm]

theorem mem_theta_upper {a : BoundLiteral (size n g.N) d} : a ∈ g.theta.upper ↔
    ∃ l ∈ g.tokUpper, a = encLit l := by
  simp [theta, eq_comm]

theorem mem_theta_bot {a : Fin (size n g.N)} : a ∈ g.theta.bot ↔ ∃ t ∈ g.tokBot, a = enc t := by
  simp [theta, eq_comm]

theorem mem_theta_top {a : Fin (size n g.N)} : a ∈ g.theta.top ↔ ∃ t ∈ g.tokTop, a = enc t := by
  simp [theta, eq_comm]

theorem origLit_lower {a : BoundLiteral n d} (ha : a ∈ g.φ.lower) :
    encLit (origLit a : Tok n g.N × _) ∈ g.theta.lower :=
  g.mem_theta_lower.mpr ⟨_, (g.mem_tokLower _).mpr (Or.inl ⟨a, ha, rfl⟩), rfl⟩

theorem origLit_upper {a : BoundLiteral n d} (ha : a ∈ g.φ.upper) :
    encLit (origLit a : Tok n g.N × _) ∈ g.theta.upper :=
  g.mem_theta_upper.mpr ⟨_, (g.mem_tokUpper _).mpr (Or.inl ⟨a, ha, rfl⟩), rfl⟩

/-- `Θ` extends `φ`: the original literals are literals of `Θ` under `orig`. -/
theorem theta_extends_lower (a : BoundLiteral n d) (ha : a ∈ g.φ.lower) :
    SubtypeConstraintOperations.renameBound (fun v => enc (Tok.orig v : Tok n g.N)) a ∈
      g.theta.lower :=
  g.origLit_lower ha

theorem theta_extends_upper (a : BoundLiteral n d) (ha : a ∈ g.φ.upper) :
    SubtypeConstraintOperations.renameBound (fun v => enc (Tok.orig v : Tok n g.N)) a ∈
      g.theta.upper :=
  g.origLit_upper ha

/-- Support of `φ` lifts to support of `Θ` (monotonicity under literal inclusion). -/
theorem support_lift {u v : Fin n} (h : Support g.POL g.φ u v) :
    Support g.POL g.theta (enc (Tok.orig u : Tok n g.N)) (enc (Tok.orig v)) :=
  support_map g.φ g.theta _ g.theta_extends_lower g.theta_extends_upper h

/-! ### Basic facts on tokens and polarities -/

@[simp] theorem sig_zero : g.sig 0 = false := by simp [sig]

theorem sig_succ {k : Nat} {i : Fin d} (h : g.w[k]? = some i) :
    g.sig (k + 1) = xor (g.sig k) (g.POL i) := by
  simp only [sig, List.take_succ, h, Option.toList_some, pathPol_append, pathPol_cons,
    pathPol_nil, Bool.xor_false]

theorem out_succ {k : Nat} {i : Fin d} (h : g.w[k]? = some i) (r : Bool) :
    g.out r (k + 1) = xor (g.out r k) (g.POL i) := by
  simp only [out, g.sig_succ h]
  cases g.sig k <;> cases g.POL i <;> cases r <;> rfl

@[simp] theorem out_zero (r : Bool) : g.out r 0 = !r := by
  cases r <;> simp [out]

theorem tokP_zero (r : Bool) : g.tokP r 0 = .orig (if r then g.y else g.x) := by
  simp [tokP]

theorem tokP_pos {r : Bool} {k : Nat} (h0 : k ≠ 0) (hk : k ≤ g.N) :
    g.tokP r k = .rail r ⟨k - 1, by omega⟩ := by
  simp [tokP, h0, show k - 1 < g.N by omega]

theorem tokP_ne_bt {r : Bool} {k : Nat} (hk : k ≤ g.N) : g.tokP r k ≠ .bt := by
  by_cases h0 : k = 0
  · subst h0; simp [tokP_zero]
  · rw [g.tokP_pos h0 hk]; simp

theorem tokP_ne_tt {r : Bool} {k : Nat} (hk : k ≤ g.N) : g.tokP r k ≠ .tt := by
  by_cases h0 : k = 0
  · subst h0; simp [tokP_zero]
  · rw [g.tokP_pos h0 hk]; simp

theorem tokP_eq_orig {r : Bool} {k : Nat} {v : Fin n} (hk : k ≤ g.N) (h : g.tokP r k = .orig v) :
    k = 0 ∧ v = (if r then g.y else g.x) := by
  by_cases h0 : k = 0
  · subst h0; rw [tokP_zero] at h; exact ⟨rfl, (Tok.orig.inj h).symm⟩
  · rw [g.tokP_pos h0 hk] at h; exact Tok.noConfusion h

theorem tokP_inj {r r' : Bool} {k k' : Nat} (h0 : k ≠ 0) (hk : k ≤ g.N) (hk' : k' ≤ g.N)
    (h : g.tokP r k = g.tokP r' k') : r = r' ∧ k = k' := by
  rw [g.tokP_pos h0 hk] at h
  by_cases h0' : k' = 0
  · subst h0'; rw [tokP_zero] at h; exact Tok.noConfusion h
  · rw [g.tokP_pos h0' hk'] at h
    simp only [Tok.rail.injEq, Fin.mk.injEq] at h
    exact ⟨h.1, by omega⟩

theorem children_rail {r : Bool} {k : Nat} {i : Fin d} (h : g.w[k]? = some i) :
    g.children r k i = g.tokP r (k + 1) := by
  simp [children, h]

theorem children_fill {r : Bool} {k : Nat} {i : Fin d} (h : g.w[k]? ≠ some i) :
    g.children r k i = g.fill (g.out r k) i := by
  simp [children, h]

theorem lt_of_getElem? {k : Nat} {i : Fin d} (h : g.w[k]? = some i) : k < g.N := by
  by_contra hk
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hk)] at h
  exact Option.noConfusion h

theorem xor_of_beq_false {a b : Bool} (h : (a == b) = false) : xor a b = true := by
  cases a <;> cases b <;> simp_all

theorem xor_of_beq_true {a b : Bool} (h : (a == b) = true) : xor a b = false := by
  cases a <;> cases b <;> simp_all

/-! ## Satisfaction: `Θ` restricts to `φ` -/

theorem theta_satisfies_restrict {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]
    (F : ContraConstructor T g.POL) (ρ : Fin (size n g.N) → T) (h : Satisfies F g.theta ρ) :
    Satisfies F g.φ (fun v => ρ (enc (Tok.orig v : Tok n g.N))) := by
  refine ⟨fun a ha => h.1 _ (g.origLit_upper ha), fun a ha => h.2.1 _ (g.origLit_lower ha),
    fun v hv => h.2.2.1 _ ?_, fun v hv => h.2.2.2 _ ?_⟩
  · exact g.mem_theta_bot.mpr ⟨_, (g.mem_tokBot _).mpr (Or.inl ⟨v, hv, rfl⟩), rfl⟩
  · exact g.mem_theta_top.mpr ⟨_, (g.mem_tokTop _).mpr (Or.inl ⟨v, hv, rfl⟩), rfl⟩

/-! ## Lemma E: every solution of `Θ` realises the failure -/

section LemmaE

theorem plabel_mono_false {s t : CTree g.POL} (h : s ≤ t) (v : List (Fin d)) :
    plabel g.POL false s.raw v ≤ plabel g.POL false t.raw v :=
  (le_iff_plabel s t).mp h v

theorem plabel_mono_true {s t : CTree g.POL} (h : s ≤ t) (v : List (Fin d)) :
    plabel g.POL true t.raw v ≤ plabel g.POL true s.raw v := by
  rw [plabel_eq_sgn true t.raw, plabel_eq_sgn true s.raw, sgn_true, sgn_true, swap_le_swap]
  exact (le_iff_plabel s t).mp h v

theorem raw_node_label (a : Fin d → CTree g.POL) : (CTree.node a).raw.label [] = 1 := rfl

theorem raw_node_project (a : Fin d → CTree g.POL) (i : Fin d) :
    project (CTree.node a).raw [i] = (a i).raw := by
  have := congrArg CTree.raw (CTree.child_node a i)
  simpa [CTree.child] using this

variable (ρ : Fin (size n g.N) → CTree g.POL)

/-- The signed rail quantity `val r k`. -/
def val (r : Bool) (k : Nat) : Label :=
  plabel g.POL (xor (g.sig k) r) (ρ (enc (g.tokP r k))).raw (g.w.drop k)

variable {ρ}

theorem lower_lit (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) {l} (hl : l ∈ g.tokLower) :
    CTree.node (fun i => ρ (enc (l.2 i))) ≤ ρ (enc l.1) :=
  hρ.2.1 (encLit l) (g.mem_theta_lower.mpr ⟨l, hl, rfl⟩)

theorem upper_lit (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) {l} (hl : l ∈ g.tokUpper) :
    ρ (enc l.1) ≤ CTree.node (fun i => ρ (enc (l.2 i))) :=
  hρ.1 (encLit l) (g.mem_theta_upper.mpr ⟨l, hl, rfl⟩)

/-- One rail step: the signed quantity does not increase. -/
theorem val_step (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) (r : Bool) {k : Nat}
    (hk : k < g.N) : g.val ρ r (k + 1) ≤ g.val ρ r k := by
  obtain ⟨i, hi⟩ : ∃ i, g.w[k]? = some i := ⟨g.w[k], List.getElem?_eq_getElem hk⟩
  have hdrop : g.w.drop k = i :: g.w.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
    rw [List.getElem?_eq_getElem hk] at hi
    rw [Option.some.inj hi]
  have hchild : g.children r k i = g.tokP r (k + 1) := g.children_rail hi
  have hlit : g.hasLit r k = true := by simp [hasLit, hk]
  have hsig := g.sig_succ hi
  unfold val
  rw [hdrop, hsig]
  set s := ρ (enc (g.tokP r k))
  set nx := ρ (enc (g.tokP r (k + 1)))
  cases ho : g.out r k
  · -- in-position: upper literal `s ≤ f(children)`
    have hmem : (g.tokP r k, g.children r k) ∈ g.tokUpper :=
      (g.mem_tokUpper _).mpr (Or.inr ⟨r, k, by omega, ho, hlit, rfl⟩)
    have hle := g.upper_lit hρ hmem
    have hμ : xor (g.sig k) r = true := xor_of_beq_false ho
    rw [hμ]
    rcases (le_iff_cases _ _).mp hle with hb | ht | ⟨a, b, hs, hn, hab⟩
    · rw [show s = ⊥ from hb, raw_bot, plabel_bot]; exact label_le_two _
    · exact absurd ht (node_ne_top _)
    · have hb : b = fun j => ρ (enc (g.children r k j)) := (CTree.node_injective hn).symm
      have hbi : b i = nx := by rw [hb]; simp [hchild, nx]
      rw [show s = CTree.node a from hs, plabel_cons_node _ _ (raw_node_label g a), raw_node_project]
      have hx : xor (xor (g.sig k) (g.POL i)) r = xor true (g.POL i) := by
        rw [← hμ]; cases g.sig k <;> cases g.POL i <;> cases r <;> rfl
      rw [hx]
      cases hp : g.POL i
      · have := (hab i).2 hp; rw [hbi] at this
        simpa using g.plabel_mono_true this (g.w.drop (k + 1))
      · have := (hab i).1 hp; rw [hbi] at this
        simpa using g.plabel_mono_false this (g.w.drop (k + 1))
  · -- out-position: lower literal `f(children) ≤ s`
    have hmem : (g.tokP r k, g.children r k) ∈ g.tokLower :=
      (g.mem_tokLower _).mpr (Or.inr ⟨r, k, by omega, ho, hlit, rfl⟩)
    have hle := g.lower_lit hρ hmem
    have hμ : xor (g.sig k) r = false := xor_of_beq_true ho
    rw [hμ]
    rcases (le_iff_cases _ _).mp hle with hb | ht | ⟨a, b, hn, hs, hab⟩
    · exact absurd hb (node_ne_bot _)
    · rw [show s = ⊤ from ht, raw_top, plabel_top]
      simp only [sgn_false]
      exact label_le_two _
    · have ha : a = fun j => ρ (enc (g.children r k j)) := (CTree.node_injective hn).symm
      have hai : a i = nx := by rw [ha]; simp [hchild, nx]
      rw [show s = CTree.node b from hs, plabel_cons_node _ _ (raw_node_label g b), raw_node_project]
      have hx : xor (xor (g.sig k) (g.POL i)) r = xor false (g.POL i) := by
        rw [← hμ]; cases g.sig k <;> cases g.POL i <;> cases r <;> rfl
      rw [hx]
      cases hp : g.POL i
      · have := (hab i).2 hp; rw [hai] at this
        simpa using g.plabel_mono_false this (g.w.drop (k + 1))
      · have := (hab i).1 hp; rw [hai] at this
        simpa using g.plabel_mono_true this (g.w.drop (k + 1))

theorem val_chain (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) (r : Bool) :
    ∀ k, k ≤ g.N → g.val ρ r k ≤ g.val ρ r 0 := by
  intro k
  induction k with
  | zero => intro _; exact le_rfl
  | succ k ih => intro hk; exact (g.val_step hρ r (by omega)).trans (ih (by omega))

theorem val_end_leaf (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) :
    g.val ρ g.leaf g.N = 2 := by
  unfold val
  rw [List.drop_length, plabel_nil]
  cases ho : g.out g.leaf g.N
  · have hmem : g.tokP g.leaf g.N ∈ g.tokBot := (g.mem_tokBot _).mpr (Or.inr (Or.inr ⟨ho, rfl⟩))
    have hb := hρ.2.2.1 _ (g.mem_theta_bot.mpr ⟨_, hmem, rfl⟩)
    have hμ : xor (g.sig g.N) g.leaf = true := xor_of_beq_false ho
    rw [hb, hμ]; rfl
  · have hmem : g.tokP g.leaf g.N ∈ g.tokTop := (g.mem_tokTop _).mpr (Or.inr (Or.inr ⟨ho, rfl⟩))
    have ht := hρ.2.2.2 _ (g.mem_theta_top.mpr ⟨_, hmem, rfl⟩)
    have hμ : xor (g.sig g.N) g.leaf = false := xor_of_beq_true ho
    rw [ht, hμ]; rfl

theorem val_end_other (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) {r : Bool}
    (hr : r ≠ g.leaf) : 1 ≤ g.val ρ r g.N := by
  unfold val
  rw [List.drop_length, plabel_nil]
  have hlit : g.hasLit r g.N = true := by simp [hasLit, hr]
  cases ho : g.out r g.N
  · have hmem : (g.tokP r g.N, g.children r g.N) ∈ g.tokUpper :=
      (g.mem_tokUpper _).mpr (Or.inr ⟨r, g.N, le_rfl, ho, hlit, rfl⟩)
    have hle := root_mono (g.upper_lit hρ hmem)
    have hμ : xor (g.sig g.N) r = true := xor_of_beq_false ho
    rw [hμ, sgn_true]
    change (ρ (enc (g.tokP r g.N))).root ≤ 1 at hle
    calc (1 : Label) = swap 1 := rfl
      _ ≤ swap (ρ (enc (g.tokP r g.N))).root := (swap_le_swap _ _).mpr hle
  · have hmem : (g.tokP r g.N, g.children r g.N) ∈ g.tokLower :=
      (g.mem_tokLower _).mpr (Or.inr ⟨r, g.N, le_rfl, ho, hlit, rfl⟩)
    have hle := root_mono (g.lower_lit hρ hmem)
    have hμ : xor (g.sig g.N) r = false := xor_of_beq_true ho
    rw [hμ, sgn_false]
    exact hle

theorem val_zero_false : g.val ρ false 0 = plabel g.POL false (ρ (enc (Tok.orig g.x))).raw g.w := by
  simp [val, tokP_zero]

theorem val_zero_true :
    g.val ρ true 0 = swap (plabel g.POL false (ρ (enc (Tok.orig g.y))).raw g.w) := by
  simp only [val, sig_zero, tokP_zero, if_true, List.drop_zero, Bool.xor_true, Bool.not_false]
  rw [plabel_eq_sgn]; rfl

/-- **Lemma E** (v1364 §5). Every solution of `Θ` makes `w` unsafe on the side, for the
restrictions to `x` and `y`: right side `plabel(ρ y, w) = B ≠ plabel(ρ x, w)`, left side
`plabel(ρ x, w) = T ≠ plabel(ρ y, w)`. -/
theorem failure (hρ : Satisfies (treeConstructor g.POL) g.theta ρ) :
    ¬ CSafe g.POL g.side (ρ (enc (Tok.orig g.x : Tok n g.N))) (ρ (enc (Tok.orig g.y))) g.w := by
  have hleaf := g.val_chain hρ g.leaf g.N le_rfl
  rw [g.val_end_leaf hρ] at hleaf
  have hother := g.val_chain hρ (!g.leaf) g.N le_rfl
  have hother' := (g.val_end_other hρ (r := !g.leaf) (by cases g.leaf <;> simp)).trans hother
  cases hs : g.side
  · -- left: leaf = X
    have hl : g.leaf = false := by simp [leaf, hs, leafRail]
    rw [hl] at hleaf hother'
    simp only [Bool.not_false] at hother'
    rw [g.val_zero_false] at hleaf
    rw [g.val_zero_true] at hother'
    intro hsafe
    simp only [CSafe] at hsafe
    have h2 := hsafe (two_le_label hleaf)
    rw [h2] at hother'
    exact absurd hother' (by decide)
  · -- right: leaf = Y
    have hl : g.leaf = true := by simp [leaf, hs, leafRail]
    rw [hl] at hleaf hother'
    simp only [Bool.not_true] at hother'
    rw [g.val_zero_true] at hleaf
    rw [g.val_zero_false] at hother'
    intro hsafe
    simp only [CSafe] at hsafe
    have h0 := hsafe (swap_eq_two.mp (two_le_label hleaf))
    rw [h0] at hother'
    exact absurd hother' (by decide)

end LemmaE

end Setup

end NSSE.ContraGadget
