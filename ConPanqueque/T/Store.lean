import ConPanqueque.T.Call
import ConPanqueque.V.View
import ConPanqueque.T.MemoRep
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
inductive Region | e (k : MemoK) | n (k : MemoNK) | c (k : CacheK) | m (b : Bool) (k : CacheK)
  deriving DecidableEq

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

def gDir := ofString "Gdir"
def gFln := ofString "Gfln"
def gFll := ofString "Gfll"
def gFls := ofString "Gfls"
def gFle := ofString "Gfle"
def gKb := ofString "Gkb"
def gHt := ofString "Ght"
/-- The active mode-memo side's descriptor offset: `0` (plain) or `EO` (eager). -/
def gEo := ofString "Geo"

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
  /-- The value heap. -/
  heap : HeapEx t C.HB C.HN C.H

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
    heapEx_frame h.heap (fun _ _ => by rw [hm]) hd (by rw [hg])⟩

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
