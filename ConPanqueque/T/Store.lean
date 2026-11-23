import ConPanqueque.T.Call
import ConPanqueque.V.View
import ConPanqueque.T.MemoRep
import ConRon.Arena.Env
import ConRon.Arena.Pins
import ConRon.Arena.WF
import ConRon.Arena.Denote
import ConRon.Bridge.StateOK
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The state relation, and the store primitives as `Spec`s

`SR C s t`: the twin state `s` is represented in the Pancake state `t` under the context `C` — the
stores (`SRep`), and the context words (layout directory, flag words, key buffer) in globals,
which a translated function's prologue copies into the locals the store code reads.
(Memos, caches and pins join later.)
-/

namespace ConPanqueque.T

/-- The memos of type `Std.HashMap (EIdx × Nat) EIdx`. -/
inductive MemoK | inst1 | instL | lift | abs1 | inst1L | instLP
  deriving DecidableEq

def memoSel : MemoK → Memos → Std.HashMap (EIdx × Nat) EIdx
  | .inst1, m => m.inst1C | .instL, m => m.instLC | .lift, m => m.liftC
  | .abs1, m => m.abs1C | .inst1L, m => m.inst1LC | .instLP, m => m.instLPC

def memoUpd : MemoK → Memos → Std.HashMap (EIdx × Nat) EIdx → Memos
  | .inst1, m, x => { m with inst1C := x } | .instL, m, x => { m with instLC := x }
  | .lift, m, x => { m with liftC := x } | .abs1, m, x => { m with abs1C := x }
  | .inst1L, m, x => { m with inst1LC := x } | .instLP, m, x => { m with instLPC := x }

theorem memoSel_upd_same (k : MemoK) (m : Memos) (x : Std.HashMap (EIdx × Nat) EIdx) :
    memoSel k (memoUpd k m x) = x := by cases k <;> rfl

theorem memoSel_upd_ne (k k' : MemoK) (h : k' ≠ k) (m : Memos) (x : Std.HashMap (EIdx × Nat) EIdx) :
    memoSel k' (memoUpd k m x) = memoSel k' m := by cases k <;> cases k' <;> first | rfl | exact absurd rfl h

/-- The `EIdx → Nat` memos. -/
inductive MemoNK | bvarB | fvarB
  deriving DecidableEq

def memoSelN : MemoNK → Memos → Std.HashMap EIdx Nat
  | .bvarB, m => m.bvarBC | .fvarB, m => m.fvarBC

def memoUpdN : MemoNK → Memos → Std.HashMap EIdx Nat → Memos
  | .bvarB, m, x => { m with bvarBC := x } | .fvarB, m, x => { m with fvarBC := x }

theorem memoSelN_upd_same (k : MemoNK) (m : Memos) (x : Std.HashMap EIdx Nat) :
    memoSelN k (memoUpdN k m x) = x := by cases k <;> rfl

theorem memoSelN_upd_ne (k k' : MemoNK) (h : k' ≠ k) (m : Memos) (x : Std.HashMap EIdx Nat) :
    memoSelN k' (memoUpdN k m x) = memoSelN k' m := by cases k <;> cases k' <;> first | rfl | exact absurd rfl h

theorem memoSel_updN (k : MemoK) (k' : MemoNK) (m : Memos) (x : Std.HashMap EIdx Nat) :
    memoSel k (memoUpdN k' m x) = memoSel k m := by cases k <;> cases k' <;> rfl

theorem memoSelN_upd (k : MemoNK) (k' : MemoK) (m : Memos) (x : Std.HashMap (EIdx × Nat) EIdx) :
    memoSelN k (memoUpd k' m x) = memoSelN k m := by cases k <;> cases k' <;> rfl

/-- The mirrored per-declaration caches of `Caches` (the entry-point tables and the instantiated-constant
tables); the readback and verdict caches are not mirrored. -/
inductive CacheK | whnfCore | whnfCoreCheap | whnf | infer | inferIO | defeq | constTy | constVal | ruleBody
  deriving DecidableEq

/-- A memo's region: one of the `(EIdx × Nat) → EIdx` memos, one of the `EIdx → Nat` ones, or a mirrored
cache. -/
inductive Region | e (k : MemoK) | n (k : MemoNK) | c (k : CacheK) | m (b : Bool) (k : CacheK) | env | tbl
  deriving DecidableEq

/-- The environment's two tables: the constants (`true`) and the projection tables (`false`). -/
def envR (b : Bool) : Region := if b then .env else .tbl

@[simp] theorem envR_ne_e (b : Bool) (k : MemoK) : envR b ≠ .e k := by cases b <;> simp [envR]
@[simp] theorem envR_ne_n (b : Bool) (k : MemoNK) : envR b ≠ .n k := by cases b <;> simp [envR]
@[simp] theorem envR_ne_c (b : Bool) (k : CacheK) : envR b ≠ .c k := by cases b <;> simp [envR]
@[simp] theorem envR_ne_m (b b' : Bool) (k : CacheK) : envR b ≠ .m b' k := by cases b <;> simp [envR]
@[simp] theorem e_ne_envR (b : Bool) (k : MemoK) : Region.e k ≠ envR b := by cases b <;> simp [envR]
@[simp] theorem n_ne_envR (b : Bool) (k : MemoNK) : Region.n k ≠ envR b := by cases b <;> simp [envR]
@[simp] theorem c_ne_envR (b : Bool) (k : CacheK) : Region.c k ≠ envR b := by cases b <;> simp [envR]
@[simp] theorem m_ne_envR (b b' : Bool) (k : CacheK) : Region.m b' k ≠ envR b := by cases b <;> simp [envR]

/-- The six mode memos (swapped by the eager tower); the other three caches are fixed. -/
def CacheK.isMode : CacheK → Bool
  | .constTy | .constVal | .ruleBody => false
  | _ => true

/-- An `EIdx → Nat` memo: key `[idxW h]`, value `ofNat n`, every value below `2^63`. -/
def encN (h : EIdx) : List (BitVec 64) := [Enc.idxW h]
def natW (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

def MemoAtN {σ : Type} (t : PanSemStateFiniteExact 64 σ) (G : BitVec 64) (g : VGeo) (m : Std.HashMap EIdx Nat) : Prop :=
  MemoAtG encN natW t G g m ∧ ∀ (k : EIdx) (v : Nat), m[k]? = some v → v < 2 ^ 63

theorem memoAtN_frame {σ : Type} {t u : PanSemStateFiniteExact 64 σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap EIdx Nat}
    (h : MemoAtN t G g m) (hm : ∀ c, inR g c → u.memory c = t.memory c)
    (hdsc : ∀ k, k < 8 → u.memory (G + BitVec.ofNat 64 (8 * k)) = t.memory (G + BitVec.ofNat 64 (8 * k)))
    (hd : u.memaddrs = t.memaddrs) : MemoAtN u G g m := ⟨memoAtG_frame h.1 hm hdsc hd, h.2⟩

/-- Keys of the pair-keyed caches. -/
def encEE (k : EIdx × EIdx) : List (BitVec 64) := [Enc.idxW k.1, Enc.idxW k.2]
def encNL (k : NIdx × LsIdx) : List (BitVec 64) := [Enc.idxW k.1, Enc.idxW k.2]
def encRB (k : NIdx × NIdx × LsIdx) : List (BitVec 64) := [Enc.idxW k.1, Enc.idxW k.2.1, Enc.idxW k.2.2]
def boolW (b : Bool) : BitVec 64 := if b then 1 else 0

structure Ctx where
  L : Layout
  FLn : BitVec 64
  FLl : BitVec 64
  FLs : BitVec 64
  FLe : BitVec 64
  KB : BitVec 64
  /-- The program's functions. -/
  code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)
  /-- Each memo's descriptor and geometry. -/
  mG : Region → BitVec 64
  mg : Region → VGeo
  /-- The value heap: base, capacity (words), and its image (the words allocated so far). -/
  HB : BitVec 64
  HN : Nat
  H : List (BitVec 64)
  /-- The eager tower: the offset from side `false` to side `true` of the mode memo descriptors, and the
  plain mode memos saved by the enclosing `enterEager` (held on side `false` while side `true` is active). -/
  EO : BitVec 64
  saved : Option ModeMemos
  /-- The environment (fixed while a declaration is checked), and its heap: base, capacity, image. -/
  fe : IFEnv
  EB : BitVec 64
  EN : Nat
  EH : List (BitVec 64)
  /-- The contents of the constant table and of the projection-table table. -/
  envM : Std.HashMap NIdx (BitVec 64)
  tblM : Std.HashMap NIdx (BitVec 64)
  /-- The pin table (filled once by the driver) and its block's index in the environment heap. -/
  pins : Pins
  PO : Nat

def gDir := ofString "Gdir"
def gFln := ofString "Gfln"
def gFll := ofString "Gfll"
def gFls := ofString "Gfls"
def gFle := ofString "Gfle"
def gKb := ofString "Gkb"
def gHt := ofString "Ght"
/-- The active mode-memo side's descriptor offset: `0` (plain) or `EO` (eager). -/
def gEo := ofString "Geo"
/-- The environment's literal flags (`natLit + 2 strLit`) and its heap top. -/
def gLit := ofString "Glit"
def gEt := ofString "Get"

/-- The value heap at `HB` (capacity `HN` words) holds the image `H`, its top in `Ght`. Values are
immutable once allocated, so facts about `H` survive every later step. -/
structure HeapAt {σ : Type} (t : PanSemStateFiniteExact 64 σ) (HB : BitVec 64) (HN : Nat) (H : List (BitVec 64)) :
    Prop where
  top : t.globals.lookup gHt = some (.val (.word (HB + BitVec.ofNat 64 (8 * H.length))))
  len : H.length ≤ HN
  lay : HB.toNat + 8 * HN < 2 ^ 64
  dom : ∀ i, i < HN → t.memaddrs (HB + BitVec.ofNat 64 (8 * i))
  val : ∀ i (hi : i < H.length), t.memory (HB + BitVec.ofNat 64 (8 * i)) = .word H[i]
  /-- Every heap cell holds a word (the free ones too), so allocation can adopt them into the image. -/
  words : ∀ i, i < HN → ∃ w, t.memory (HB + BitVec.ofNat 64 (8 * i)) = .word w

/-- The heap holds some extension of the image `H` (later allocations are invisible to a context that
fixed `H`). -/
def HeapEx {σ : Type} (t : PanSemStateFiniteExact 64 σ) (HB : BitVec 64) (HN : Nat) (H : List (BitVec 64)) : Prop :=
  ∃ H', H <+: H' ∧ HeapAt t HB HN H'

theorem heapAt_frame {σ : Type} {t u : PanSemStateFiniteExact 64 σ} {HB : BitVec 64} {HN : Nat}
    {H : List (BitVec 64)} (h : HeapAt t HB HN H)
    (hm : ∀ i, i < HN → u.memory (HB + BitVec.ofNat 64 (8 * i)) = t.memory (HB + BitVec.ofNat 64 (8 * i)))
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals.lookup gHt = t.globals.lookup gHt) : HeapAt u HB HN H :=
  ⟨by rw [hg]; exact h.top, h.len, h.lay, fun i hi => by rw [hd]; exact h.dom i hi,
    fun i hi => by rw [hm i (Nat.lt_of_lt_of_le hi h.len)]; exact h.val i hi,
    fun i hi => by rw [hm i hi]; exact h.words i hi⟩

theorem heapEx_frame {σ : Type} {t u : PanSemStateFiniteExact 64 σ} {HB : BitVec 64} {HN : Nat}
    {H : List (BitVec 64)} (h : HeapEx t HB HN H)
    (hm : ∀ i, i < HN → u.memory (HB + BitVec.ofNat 64 (8 * i)) = t.memory (HB + BitVec.ofNat 64 (8 * i)))
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals.lookup gHt = t.globals.lookup gHt) : HeapEx u HB HN H :=
  let ⟨H', hp, ha⟩ := h; ⟨H', hp, heapAt_frame ha hm hd hg⟩

variable {σ : Type}

/-- The fixed cache `k` in memory (the mode memos are `ModeAt`'s). -/
def CacheAt (t : PState σ) (C : Ctx) (cs : Caches) : CacheK → Prop
  | .whnfCore | .whnfCoreCheap | .whnf | .infer | .inferIO | .defeq => True
  | .constTy => MemoAtG encNL Enc.idxW t (C.mG (.c .constTy)) (C.mg (.c .constTy)) cs.constTyC
  | .constVal => MemoAtG encNL Enc.idxW t (C.mG (.c .constVal)) (C.mg (.c .constVal)) cs.constValC
  | .ruleBody => MemoAtG encRB Enc.idxW t (C.mG (.c .ruleBody)) (C.mg (.c .ruleBody)) cs.ruleBodyC

theorem cacheAt_frame {C : Ctx} {cs : Caches} {t u : PState σ} {k : CacheK} (h : CacheAt t C cs k)
    (hm : ∀ c, inR (C.mg (.c k)) c → u.memory c = t.memory c)
    (hdsc : ∀ j, j < 8 → u.memory (C.mG (.c k) + BitVec.ofNat 64 (8 * j)) =
      t.memory (C.mG (.c k) + BitVec.ofNat 64 (8 * j)))
    (hd : u.memaddrs = t.memaddrs) : CacheAt u C cs k := by
  cases k <;> first | trivial | exact memoAtG_frame h hm hdsc hd

/-- Mode memo `k` of the set `mm`, on side `b`. -/
def CacheAtM (t : PState σ) (C : Ctx) (b : Bool) (mm : ModeMemos) : CacheK → Prop
  | .whnfCore => MemoAtG encN Enc.idxW t (C.mG (.m b .whnfCore)) (C.mg (.m b .whnfCore)) mm.whnfCoreC
  | .whnfCoreCheap => MemoAtG encN Enc.idxW t (C.mG (.m b .whnfCoreCheap)) (C.mg (.m b .whnfCoreCheap)) mm.whnfCoreCheapC
  | .whnf => MemoAtG encN Enc.idxW t (C.mG (.m b .whnf)) (C.mg (.m b .whnf)) mm.whnfC
  | .infer => MemoAtG encN Enc.idxW t (C.mG (.m b .infer)) (C.mg (.m b .infer)) mm.inferC
  | .inferIO => MemoAtG encN Enc.idxW t (C.mG (.m b .inferIO)) (C.mg (.m b .inferIO)) mm.inferIOC
  | .defeq => MemoAtG encEE boolW t (C.mG (.m b .defeq)) (C.mg (.m b .defeq)) mm.defeqC
  | .constTy | .constVal | .ruleBody => True

def SideAt (t : PState σ) (C : Ctx) (b : Bool) (mm : ModeMemos) : Prop := ∀ k, CacheAtM t C b mm k

/-- The active side: `true` inside an eager comparison (the context holds the saved plain memos). -/
def Ctx.side (C : Ctx) : Bool := C.saved.isSome

/-- The active side's descriptor offset, held in `gEo`. -/
def Ctx.eo (C : Ctx) : BitVec 64 := if C.saved.isSome then C.EO else 0

/-- The eager tower. Plain (`C.saved = none`, `gEo = 0`): side `false` holds the active mode memos and side
`true` the stored eager ones. Eager (`C.saved = some mm`, `gEo = EO`): side `true` holds the active (eager)
memos, side `false` the plain ones `mm` the enclosing `enterEager` saved, and the twin's eager slot is empty. -/
def ModeAt (t : PState σ) (C : Ctx) (cs : Caches) : Prop :=
  t.globals.lookup gEo = some (.val (.word C.eo)) ∧ SideAt t C C.side cs.modeMemos ∧
  match C.saved with
  | none => SideAt t C true cs.eagerMemos
  | some mm => SideAt t C false mm ∧ cs.eagerMemos = ModeMemos.empty

theorem sideAt_frame {C : Ctx} {mm : ModeMemos} {t u : PState σ} {b : Bool} (h : SideAt t C b mm)
    (hm : ∀ k c, inR (C.mg (.m b k)) c → u.memory c = t.memory c)
    (hdsc : ∀ k j, j < 8 → u.memory (C.mG (.m b k) + BitVec.ofNat 64 (8 * j)) =
      t.memory (C.mG (.m b k) + BitVec.ofNat 64 (8 * j)))
    (hd : u.memaddrs = t.memaddrs) : SideAt u C b mm := by
  intro k
  have hk := h k
  cases k <;> first | trivial | exact memoAtG_frame hk (hm _) (hdsc _) hd

theorem modeAt_frame {C : Ctx} {cs : Caches} {t u : PState σ} (h : ModeAt t C cs)
    (hm : ∀ b k c, inR (C.mg (.m b k)) c → u.memory c = t.memory c)
    (hdsc : ∀ b k j, j < 8 → u.memory (C.mG (.m b k) + BitVec.ofNat 64 (8 * j)) =
      t.memory (C.mG (.m b k) + BitVec.ofNat 64 (8 * j)))
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals.lookup gEo = t.globals.lookup gEo) : ModeAt u C cs := by
  obtain ⟨g, h1, h2⟩ := h
  refine ⟨by rw [hg]; exact g, sideAt_frame h1 (hm _) (hdsc _) hd, ?_⟩
  revert h2
  cases C.saved with
  | none => exact fun h2 => sideAt_frame h2 (hm _) (hdsc _) hd
  | some mm => exact fun ⟨h2, h3⟩ => ⟨sideAt_frame h2 (hm _) (hdsc _) hd, h3⟩

/-- Two cache records agree on the mirrored tables. -/
def MirrorEq (a b : Caches) : Prop :=
  a.modeMemos = b.modeMemos ∧ a.eagerMemos = b.eagerMemos ∧ a.constTyC = b.constTyC ∧ a.constValC = b.constValC ∧
    a.ruleBodyC = b.ruleBodyC

theorem mirrorEq_refl (a : Caches) : MirrorEq a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mirrorEq_trans {a b c : Caches} (h1 : MirrorEq a b) (h2 : MirrorEq b c) : MirrorEq a c := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5⟩

theorem cacheAt_mirror {C : Ctx} {a b : Caches} {t : PState σ} {k : CacheK} (h : CacheAt t C b k)
    (he : MirrorEq a b) : CacheAt t C a k := by
  obtain ⟨_, _, e7, e8, e9⟩ := he
  cases k <;> simp only [CacheAt] at h ⊢
  · rw [e7]; exact h
  · rw [e8]; exact h
  · rw [e9]; exact h

theorem modeAt_mirror {C : Ctx} {a b : Caches} {t : PState σ} (h : ModeAt t C b) (he : MirrorEq a b) :
    ModeAt t C a := by
  obtain ⟨e1, e2, _, _, _⟩ := he
  unfold ModeAt; rw [e1, e2]; exact h

/-! ## The environment -/

def ecell (C : Ctx) (j : Nat) : BitVec 64 := C.EB + BitVec.ofNat 64 (8 * j)

/-- An environment-heap block `[n, x₀, …]` at index `o`. -/
def EBlk (H : List (BitVec 64)) (o : Nat) (xs : List (BitVec 64)) : Prop :=
  H[o]? = some (BitVec.ofNat 64 xs.length) ∧ ∀ i (hi : i < xs.length), H[o + 1 + i]? = some xs[i]

/-- A word naming a block of handles. -/
def ENList {k : IdxKind} (EB : BitVec 64) (H : List (BitVec 64)) (w : BitVec 64) (xs : List (Idx k)) : Prop :=
  ∃ o, w = EB + BitVec.ofNat 64 (8 * o) ∧ EBlk H o (xs.map Enc.idxW)

/-- A natural number field (below `2^63`). -/
def NatE (H : List (BitVec 64)) (i n : Nat) : Prop := H[i]? = some (BitVec.ofNat 64 n) ∧ n < 2 ^ 63

def hintN : ConLeche.ReducibilityHint → Nat
  | .opaque => 0 | .abbrev => 1 | .regular h => h + 2

def CVE (EB : BitVec 64) (H : List (BitVec 64)) (o : Nat) (v : IConstantVal) : Prop :=
  H[o]? = some (Enc.idxW v.name) ∧ (∃ w, H[o + 1]? = some w ∧ ENList EB H w v.levelParams) ∧
    H[o + 2]? = some (Enc.idxW v.type)

def FireE (EB : BitVec 64) (H : List (BitVec 64)) (o : Nat) : IRecRuleFire → Prop
  | .plain => H[o]? = some 0
  | .nested lv pins => H[o]? = some 1 ∧ (∃ w, H[o + 1]? = some w ∧ ENList EB H w lv) ∧
      ∃ w, H[o + 2]? = some w ∧ ENList EB H w pins
  | .levels lv => H[o]? = some 2 ∧ ∃ w, H[o + 1]? = some w ∧ ENList EB H w lv

/-- A recursor rule `[ctor, nfields, fireTag, fire₁, fire₂, rhs]`. -/
def RuleE (EB : BitVec 64) (H : List (BitVec 64)) (o : Nat) (r : IRecRule) : Prop :=
  H[o]? = some (Enc.idxW r.ctor) ∧ NatE H (o + 1) r.nfields ∧ FireE EB H (o + 2) r.fire ∧
    H[o + 5]? = some (Enc.idxW r.rhs)

/-- A block of rule pointers. -/
def RulesE (EB : BitVec 64) (H : List (BitVec 64)) (w : BitVec 64) (rs : List IRecRule) : Prop :=
  ∃ o, w = EB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some (BitVec.ofNat 64 rs.length) ∧
    ∀ i (hi : i < rs.length), ∃ q, H[o + 1 + i]? = some (EB + BitVec.ofNat 64 (8 * q)) ∧ RuleE EB H q rs[i]

/-- A stored constant at index `o`: `[tag, name, levelParams, type, fields…]`. -/
def CIE (EB : BitVec 64) (H : List (BitVec 64)) (o : Nat) (ci : IConstantInfo) : Prop :=
  CVE EB H (o + 1) ci.toConstantVal ∧
  match ci with
  | .axiomInfo _ => H[o]? = some 0
  | .defnInfo _ val hint => H[o]? = some 1 ∧ H[o + 4]? = some (Enc.idxW val) ∧ NatE H (o + 5) (hintN hint)
  | .thmInfo _ => H[o]? = some 2
  | .indInfo _ caps => H[o]? = some 3 ∧ H[o + 4]? = some (boolW caps.eta) ∧
      (∃ w, H[o + 5]? = some w ∧ ENList EB H w caps.all) ∧ NatE H (o + 6) caps.nparams ∧
      NatE H (o + 7) caps.nIdx ∧ (∃ w, H[o + 8]? = some w ∧ ENList EB H w caps.ctors) ∧
      H[o + 9]? = some (boolW caps.neverZero)
  | .ctorInfo _ np nf ind => H[o]? = some 4 ∧ NatE H (o + 4) np ∧ NatE H (o + 5) nf ∧
      H[o + 6]? = some (Enc.idxW ind)
  | .recInfo _ mi rp isK rules => H[o]? = some 5 ∧ NatE H (o + 4) mi ∧ NatE H (o + 5) rp ∧
      H[o + 6]? = some (boolW isK) ∧ ∃ w, H[o + 7]? = some w ∧ RulesE EB H w rules

/-- A projection table `[structName, levelParams, numParams, ctor, numFields, bodies]`. -/
def TblE (EB : BitVec 64) (H : List (BitVec 64)) (o : Nat) (t : IProjTable) : Prop :=
  H[o]? = some (Enc.idxW t.structName) ∧ (∃ w, H[o + 1]? = some w ∧ ENList EB H w t.levelParams) ∧
    NatE H (o + 2) t.numParams ∧ H[o + 3]? = some (Enc.idxW t.ctor) ∧ NatE H (o + 4) t.numFields ∧
    ∃ w, H[o + 5]? = some w ∧ ENList EB H w t.bodies.toList

/-- A name-keyed table key. -/
def encNI (n : NIdx) : List (BitVec 64) := [Enc.idxW n]

def litW (fe : IFEnv) : BitVec 64 := boolW fe.natLit + 2 * boolW fe.strLit

/-- The environment heap at `EB` (capacity `EN`) holds the image `EH` (every cell a word), its top in `gEt`. -/
structure EHeapAt (t : PState σ) (EB : BitVec 64) (EN : Nat) (EH : List (BitVec 64)) : Prop where
  top : t.globals.lookup gEt = some (.val (.word (EB + BitVec.ofNat 64 (8 * EH.length))))
  len : EH.length ≤ EN
  lay : EB.toNat + 8 * EN < 2 ^ 64
  dom : ∀ i, i < EN → t.memaddrs (EB + BitVec.ofNat 64 (8 * i))
  val : ∀ i (hi : i < EH.length), t.memory (EB + BitVec.ofNat 64 (8 * i)) = .word EH[i]
  words : ∀ i, i < EN → ∃ w, t.memory (EB + BitVec.ofNat 64 (8 * i)) = .word w

/-- The ghost tables represent the environment: the constant table answers `find?`, the other
`findTable?`, with blocks in the environment heap. (Static: a `CtxOK` fact.) -/
def EnvRel (C : Ctx) : Prop :=
  (∀ n, match C.fe.find? n with
    | none => C.envM[n]? = none
    | some ci => ∃ o, C.envM[n]? = some (ecell C o) ∧ CIE C.EB C.EH o ci) ∧
  (∀ n, match C.fe.findTable? n with
    | none => C.tblM[n]? = none
    | some tb => ∃ o, C.tblM[n]? = some (ecell C o) ∧ TblE C.EB C.EH o tb)

/-- The pin table's block at `PO`: the `pinCount` names, then `emptyLevels`, `zeroLevel`, `sortOne`,
`maxNatSize` and the reserved-name list. (Static: a `CtxOK` fact.) -/
def PinsE (C : Ctx) : Prop :=
  C.pins.names.size = pinCount ∧
  (∀ i (hi : i < C.pins.names.size), C.EH[C.PO + i]? = some (Enc.idxW C.pins.names[i])) ∧
  C.EH[C.PO + pinCount]? = some (Enc.idxW C.pins.emptyLevels) ∧
  C.EH[C.PO + pinCount + 1]? = some (Enc.idxW C.pins.zeroLevel) ∧
  C.EH[C.PO + pinCount + 2]? = some (Enc.idxW C.pins.sortOne) ∧
  NatE C.EH (C.PO + pinCount + 3) C.pins.maxNatSize ∧
  ∃ w, C.EH[C.PO + pinCount + 4]? = some w ∧ ENList C.EB C.EH w C.pins.reserved

/-- The environment `C.fe` in memory: its heap, the constant table (name ↦ the constant's block) and the
projection-table table (structure name ↦ its table's block, exactly where `findTable?` answers), and the
literal flags. -/
def EnvAt (t : PState σ) (C : Ctx) : Prop :=
  EHeapAt t C.EB C.EN C.EH ∧
  MemoAtG encNI id t (C.mG .env) (C.mg .env) C.envM ∧
  MemoAtG encNI id t (C.mG .tbl) (C.mg .tbl) C.tblM ∧
  t.globals.lookup gLit = some (.val (.word (litW C.fe)))

theorem envAt_frame {C : Ctx} {t u : PState σ} (h : EnvAt t C)
    (hT : ∀ b c, inR (C.mg (envR b)) c → u.memory c = t.memory c)
    (hTd : ∀ b j, j < 8 → u.memory (C.mG (envR b) + BitVec.ofNat 64 (8 * j)) =
      t.memory (C.mG (envR b) + BitVec.ofNat 64 (8 * j)))
    (hE : ∀ i, i < C.EN → u.memory (ecell C i) = t.memory (ecell C i))
    (hd : u.memaddrs = t.memaddrs)
    (hg : u.globals.lookup gLit = t.globals.lookup gLit ∧ u.globals.lookup gEt = t.globals.lookup gEt) :
    EnvAt u C := by
  obtain ⟨hH, hm, hm', hl⟩ := h
  refine ⟨⟨by rw [hg.2]; exact hH.top, hH.len, hH.lay, fun i hi => by rw [hd]; exact hH.dom i hi,
      fun i hi => by
        have e := hE i (Nat.lt_of_lt_of_le hi hH.len); unfold ecell at e; rw [e]; exact hH.val i hi,
      fun i hi => by have e := hE i hi; unfold ecell at e; rw [e]; exact hH.words i hi⟩,
    memoAtG_frame hm (hT true) (hTd true) hd, memoAtG_frame hm' (hT false) (hTd false) hd,
    by rw [hg.1]; exact hl⟩

/-- The twin-only read and comparison caches agree with the store's denotations. -/
structure CachesOK (s : AState) : Prop where
  rn : ConRon.Bridge.ReadNCacheOK s.caches.readNC s.store
  rl : ConRon.Bridge.ReadLCacheOK s.caches.readLC s.store
  rls : ConRon.Bridge.ReadLsCacheOK s.caches.readLsC s.store
  le : ConRon.Bridge.LvlEqCacheOK s.caches.lvlEqC s.store
  les : ConRon.Bridge.LvlsEqCacheOK s.caches.lvlsEqC s.store

theorem cachesOK_ext {s s' : AState} (h : CachesOK s) (hx : Ext s.store s'.store) (hc : s'.caches = s.caches) :
    CachesOK s' := by
  obtain ⟨rn, rl, rls, le, les⟩ := h
  refine ⟨fun k x hk => ?_, fun k u hk => ?_, fun k us hk => ?_, fun k r hk => ?_, fun k r hk => ?_⟩
  · rw [hc] at hk; exact hx.lss.ls.ns _ _ (rn k x hk)
  · rw [hc] at hk; exact hx.lss.ls.lvl _ _ (rl k u hk)
  · rw [hc] at hk; exact hx.lss.lst _ _ (rls k us hk)
  · rw [hc] at hk; obtain ⟨u, v, h1, h2, h3⟩ := le k r hk
    exact ⟨u, v, hx.lss.ls.lvl _ _ h1, hx.lss.ls.lvl _ _ h2, h3⟩
  · rw [hc] at hk; obtain ⟨u, v, h1, h2, h3⟩ := les k r hk
    exact ⟨u, v, hx.lss.lst _ _ h1, hx.lss.lst _ _ h2, h3⟩

theorem cachesOK_congr {s s' : AState} (h : CachesOK s) (hs : s'.store = s.store)
    (hc : s'.caches.readNC = s.caches.readNC ∧ s'.caches.readLC = s.caches.readLC ∧
      s'.caches.readLsC = s.caches.readLsC ∧ s'.caches.lvlEqC = s.caches.lvlEqC ∧
      s'.caches.lvlsEqC = s.caches.lvlsEqC) : CachesOK s' := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  obtain ⟨rn, rl, rls, le, les⟩ := h
  exact ⟨by rw [c1, hs]; exact rn, by rw [c2, hs]; exact rl, by rw [c3, hs]; exact rls, by rw [c4, hs]; exact le,
    by rw [c5, hs]; exact les⟩

theorem cachesOK_readLC {s : AState} (h : CachesOK s) (X : Std.HashMap LIdx ConLeche.Level)
    (hX : ConRon.Bridge.ReadLCacheOK X s.store) : CachesOK { s with caches := { s.caches with readLC := X } } :=
  ⟨h.rn, hX, h.rls, h.le, h.les⟩

theorem cachesOK_readLsC {s : AState} (h : CachesOK s) (X : Std.HashMap LsIdx (List ConLeche.Level))
    (hX : ConRon.Bridge.ReadLsCacheOK X s.store) : CachesOK { s with caches := { s.caches with readLsC := X } } :=
  ⟨h.rn, h.rl, hX, h.le, h.les⟩

theorem cachesOK_caches {s : AState} (h : CachesOK s) (c : Caches)
    (hc : c = { s.caches with readNC := c.readNC }) (hN : ConRon.Bridge.ReadNCacheOK c.readNC s.store) :
    CachesOK { s with caches := c } := by
  obtain ⟨rn, rl, rls, le, les⟩ := h
  refine ⟨hN, ?_, ?_, ?_, ?_⟩ <;> rw [hc] <;> assumption

theorem cachesOK_cachesLs {s : AState} (h : CachesOK s) (c : Caches)
    (hc : c = { s.caches with readLsC := c.readLsC }) (hX : ConRon.Bridge.ReadLsCacheOK c.readLsC s.store) :
    CachesOK { s with caches := c } := by
  obtain ⟨rn, rl, rls, le, les⟩ := h
  refine ⟨?_, ?_, hX, ?_, ?_⟩ <;> rw [hc] <;> assumption

/-- The environment's stored constants denote in the twin store: their level-parameter names and their types. -/
/-- Every constant's level parameters and type denote, its level-parameter count is small, and a definition's
value denotes. -/
def ConstDen (fe : IFEnv) (st : EStore) : Prop :=
  ∀ c ci, fe.find? c = some ci → (∀ n ∈ ci.toConstantVal.levelParams, (denoteN st.ns n).isSome = true) ∧
    (denoteE st ci.toConstantVal.type).isSome = true ∧ ci.toConstantVal.levelParams.length + 1 < 2 ^ 60 ∧
    (∀ cv v hint, ci = .defnInfo cv v hint → (denoteE st v).isSome = true)

/-- Every projection table's level parameters and bodies denote, and its level-parameter count is small. -/
def TblDen (fe : IFEnv) (st : EStore) : Prop :=
  ∀ T tbl, fe.findTable? T = some tbl → (∀ n ∈ tbl.levelParams, (denoteN st.ns n).isSome = true) ∧
    (∀ b ∈ tbl.bodies.toList, (denoteE st b).isSome = true) ∧ tbl.levelParams.length + 1 < 2 ^ 60

def EnvDen (fe : IFEnv) (st : EStore) : Prop := ConstDen fe st ∧ TblDen fe st

theorem denoteN_isSome_ext {st st' : EStore} (hx : Ext st st') {n : NIdx} (h : (denoteN st.ns n).isSome = true) :
    (denoteN st'.ns n).isSome = true := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
  show (denoteN st'.lss.ls.ns n).isSome = true
  rw [hx.lss.ls.ns n m hm]; rfl

theorem denoteE_isSome_ext {st st' : EStore} (hx : Ext st st') {e : EIdx} (h : (denoteE st e).isSome = true) :
    (denoteE st' e).isSome = true := by
  obtain ⟨x, hx'⟩ := Option.isSome_iff_exists.mp h
  rw [hx.expr _ x hx']; rfl

theorem envDen_ext {fe : IFEnv} {st st' : EStore} (h : EnvDen fe st) (hx : Ext st st') : EnvDen fe st' := by
  refine ⟨fun c ci hc => ?_, fun T tbl hT => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.1 c ci hc
    exact ⟨fun n hn => denoteN_isSome_ext hx (h1 n hn), denoteE_isSome_ext hx h2, h3,
      fun cv v hint hci => denoteE_isSome_ext hx (h4 cv v hint hci)⟩
  · obtain ⟨h1, h2, h3⟩ := h.2 T tbl hT
    exact ⟨fun n hn => denoteN_isSome_ext hx (h1 n hn), fun b hb => denoteE_isSome_ext hx (h2 b hb), h3⟩

structure SR (C : Ctx) (s : AState) (t : PState σ) : Prop where
  rep : SRep t C.L C.FLn C.FLl C.FLs C.FLe s.store
  gdir : t.globals.lookup gDir = some (.val (.word C.L.DIR))
  gfln : t.globals.lookup gFln = some (.val (.word C.FLn))
  gfll : t.globals.lookup gFll = some (.val (.word C.FLl))
  gfls : t.globals.lookup gFls = some (.val (.word C.FLs))
  gfle : t.globals.lookup gFle = some (.val (.word C.FLe))
  gkb : t.globals.lookup gKb = some (.val (.word C.KB))
  code : t.code = C.code
  /-- The key buffer's words are addressable (keys of up to three words; longer ones later). -/
  kbuf : ∀ j, j < 3 → t.memaddrs (C.KB + BitVec.ofNat 64 (8 * j))
  /-- The memos. -/
  memo : ∀ k, MemoAt t (C.mG (.e k)) (C.mg (.e k)) (memoSel k s.memos)
  /-- The `EIdx → Nat` memos. -/
  memoN : ∀ k, MemoAtN t (C.mG (.n k)) (C.mg (.n k)) (memoSelN k s.memos)
  /-- The mirrored caches. -/
  cache : ∀ k, CacheAt t C s.caches k
  /-- The mode memos and the eager tower. -/
  mode : ModeAt t C s.caches
  /-- The environment. -/
  env : EnvAt t C
  /-- The pin table is the context's. -/
  pins : s.pins = C.pins
  /-- The value heap. -/
  heap : HeapEx t C.HB C.HN C.H
  /-- The twin store is well formed (con-ron's `StoreWF`). -/
  twf : StoreWF s.store
  /-- The environment's constants denote in the twin store. -/
  envd : EnvDen C.fe s.store
  /-- The twin-only caches are correct. -/
  cok : CachesOK s

theorem sr_of_eq {C : Ctx} {s : AState} {t u : PState σ} (h : SR C s t) (hm : u.memory = t.memory)
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals = t.globals) (hc : u.code = t.code) : SR C s u :=
  ⟨srep_frame h.rep ⟨by rw [hm], by rw [hm], by rw [hm], by rw [hm]⟩ hd
      (fun _ _ _ _ => ⟨fun _ _ => by rw [hm], fun _ _ => by rw [hm]⟩),
    by rw [hg]; exact h.gdir, by rw [hg]; exact h.gfln, by rw [hg]; exact h.gfll, by rw [hg]; exact h.gfls,
    by rw [hg]; exact h.gfle, by rw [hg]; exact h.gkb, by rw [hc]; exact h.code,
    fun j hj => by rw [hd]; exact h.kbuf j hj, fun k => memoAt_of_eq (h.memo k) hm hd,
    fun k => memoAtN_frame (h.memoN k) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd,
    fun k => cacheAt_frame (h.cache k) (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd,
    modeAt_frame h.mode (fun _ _ _ _ => by rw [hm]) (fun _ _ _ _ => by rw [hm]) hd (by rw [hg]),
    envAt_frame h.env (fun _ _ _ => by rw [hm]) (fun _ _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd
      ⟨by rw [hg], by rw [hg]⟩, h.pins,
    heapEx_frame h.heap (fun _ _ => by rw [hm]) hd (by rw [hg]), h.twf, h.envd, h.cok⟩

theorem eval_gv (t : PState σ) (g : MlS) (w : BitVec 64) (h : t.globals.lookup g = some (.val (.word w))) :
    EV t (.var .global g) = some (.val (.word w)) := by
  simp [EV, evalHOLExact, h]

/-! ## Local declarations -/

theorem specR_dec {α : Type} {P P1 : PState σ → Prop} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (body : ProgHOL 64)
    (v : PState σ → BitVec 64) (he : ∀ t, P t → EV t e = some (.val (.word (v t))))
    (h : SpecR P1 body s m R) (hP : ∀ t, P t → P1 (setVarHOLFinite x (.val (.word (v t))) t))
    (hR : ∀ a w s' st (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L }) :
    SpecR P (.dec x .one e body) s m R := by
  intro t ht
  rw [dec_word_eq t x e (v t) body (he t ht)]
  rcases h _ (hP t ht) with hs | ⟨w, hr, a, s', hm, hR'⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', hm, hR _ _ _ _ _ hR'⟩

/-! ## `app` handles -/

theorem view_app_some (st : EStore) (i : EIdx) (f a : EIdx) (h4 : i.tag = 4) (hv : st.view i = some (.app f a)) :
    st.viewApp i = some (f, a) := by
  have hw : i.isWide = true := by
    cases hw : i.isWide
    · exfalso
      simp only [EStore.view] at hv
      split at hv
      · simp [ETables.get, h4, hw, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at hv
      · split at hv
        · simp [ETables.get, h4, hw, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at hv
        · exact absurd hv (by simp)
    · rfl
  simp only [EStore.view] at hv
  simp only [EStore.viewApp, EStore.persGetApp]
  split
  · rename_i hp; rw [if_pos hp] at hv
    simp only [ETables.get, h4, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, hw] at hv
    simp only [ETables.getApp, hw, ↓reduceIte]
    revert hv; cases st.pers.apps.node? i.idxNat <;> simp
  · rename_i hp; rw [if_neg hp] at hv
    split
    · rename_i hon; rw [if_pos hon] at hv
      simp only [ETables.get, h4, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, hw] at hv
      simp only [ETables.getApp, hw, ↓reduceIte]
      revert hv; cases st.scr.apps.node? i.idxNat <;> simp
    · rename_i hon; rw [if_neg hon] at hv; exact absurd hv (by simp)

theorem viewApp_run (h : EIdx) (s : AState) : ConRon.Arena.viewApp h s = .ok (s.store.viewApp h, s) := rfl

/-- The twin's `viewApp h` at an `app`-tagged handle, by the expression view; the fields are at `rp`. -/
theorem spec_viewApp {C : Ctx} {s : AState} {P : PState σ → Prop} {Q : Option (EIdx × EIdx) → AState → PState σ → Prop}
    (h : EIdx) (h4 : h.tag = 4)
    (hP : ∀ t, P t → SR C s t ∧ t.locals.lookup lDh = some (.val (.word (Enc.idxW h))) ∧
      t.locals.lookup lDir = some (.val (.word C.L.DIR)) ∧ t.locals.lookup lFl = some (.val (.word C.FLe)) ∧
      (∃ w, t.locals.lookup lDt = some (.val (.word w))) ∧ (∃ w, t.locals.lookup lDg = some (.val (.word w))) ∧
      (∃ w, t.locals.lookup lDi = some (.val (.word w))) ∧ (∃ w, t.locals.lookup lRp = some (.val (.word w))) ∧
      (∃ w, t.locals.lookup lRn = some (.val (.word w))))
    (hQ : ∀ t, P t → ∀ f a, RowRes t h.tier.toNat h.tag.toNat h.idxNat (Enc.encApp ⟨f, a⟩) (evaluateHOLFiniteState t eViewP) →
      Q (some (f, a)) s (evaluateHOLFiniteState t eViewP).2) :
    Spec P eViewP s (ConRon.Arena.viewApp h) Q := by
  intro t ht
  obtain ⟨hsr, hh, hdir, hfl, ht', hg, hi, h1, h2⟩ := hP t ht
  rcases eView_spec t C.L C.FLe s.store hsr.rep.e h hh hdir hfl ht' hg hi h1 h2 with hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl hs
  rw [h4] at htg
  cases v with
  | app f a =>
    right
    refine ⟨hr.1, some (f, a), s, ?_, hQ t ht f a hr⟩
    rw [viewApp_run, view_app_some s.store h f a h4 hv]
  | _ => simp [ENodeView.tagN] at htg

/-- `var x₁ = 0; …; var xₙ = 0; body`. -/
def decs0 : List MlS → ProgHOL 64 → ProgHOL 64
  | [], b => b
  | x :: xs, b => .dec x .one (.const 0) (decs0 xs b)

/-- `t'` is `t` with the locals `xs` freshly zeroed. -/
def Zeroed (xs : List MlS) (t t' : PState σ) : Prop :=
  t'.memory = t.memory ∧ t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧ t'.code = t.code ∧
    (∀ y, y ∉ xs → t'.locals.lookup y = t.locals.lookup y) ∧
    (∀ x, x ∈ xs → t'.locals.lookup x = some (.val (.word 0)))

theorem specR_decs0 {α : Type} {s : AState} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hR : ∀ a w s' st (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L })
    (body : ProgHOL 64) (I : PState σ → Prop) (h : SpecR I body s m R) :
    ∀ (xs : List MlS) (P : PState σ → Prop), (∀ t, P t → ∀ t', Zeroed xs t t' → I t') → SpecR P (decs0 xs body) s m R
  | [], P, hP => fun t ht => h t (hP t ht t ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ hx => absurd hx (by simp)⟩)
  | x :: xs, P, hP => by
    refine specR_dec x (.const 0) (decs0 xs body) (fun _ => 0) (fun t _ => by simp [EV, evalHOLExact])
      (specR_decs0 hR body I h xs (fun u => ∃ t, P t ∧ u = setVarHOLFinite x (.val (.word 0)) t) ?_)
      (fun t ht => ⟨t, ht, rfl⟩) hR
    rintro u ⟨t, ht, rfl⟩ t' ⟨m1, d1, g1, c1, fr1, z1⟩
    refine hP t ht t' ⟨m1, d1, g1, c1, fun y hy => ?_, fun z hz => ?_⟩
    · simp only [List.mem_cons, not_or] at hy
      rw [fr1 y hy.2]; exact lookup_setVar_other _ _ hy.1
    · by_cases hzx : z ∈ xs
      · exact z1 z hzx
      · simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · rw [fr1 _ hzx]; exact lookup_setVar_same _ _ _
        · exact absurd hz hzx

end ConPanqueque.T
