import ConPanqueque.Start.InitSR

/-! # The bootstrap context and its invariant

`C0 code`: the concrete layout with the bootstrap store as floor, the placeholder pins `P0`, the
start environment of `P0`, the placeholder environment heap `EH0`, and a value heap of `NH` zero
words.  `InitGlobals`: the globals as the program declares them.  `sr_init`: after the initial
stores, `SR (C0 code) (sBoot P0)` holds. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConRon.Arena ConRon.Bridge ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code

namespace ConPanqueque.Start

variable {σ : Type}

set_option maxRecDepth 100000

/-- The frontend's area in the value heap: the three name/level/expression tables (`cap` each),
the declaration registry (`capD`), then the input buffer (`Lw` words, a length header first). -/
def capF : Nat := 2 ^ 20
def capD : Nat := 2 ^ 18
def Lw : Nat := 2 ^ 24
def rbF : Nat := 3 * capF
def j0F : Nat := rbF + capD
def NH : Nat := j0F + Lw

def Himg : List (BitVec 64) := List.replicate NH 0

abbrev Code := HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)

def C0 (code : Code) : Ctx := ctxOf code Himg none bootStore (feStart P0) EH0 ∅ ∅ P0 PO0

structure InitGlobals (t : PanSemStateFiniteExact 64 σ) (code : Code) : Prop where
  code : t.code = code
  dir : t.globals.lookup gDir = some (.val (.word (BitVec.ofNat 64 base)))
  fln : t.globals.lookup gFln = some (.val (.word (BitVec.ofNat 64 (base + 4096))))
  fll : t.globals.lookup gFll = some (.val (.word (BitVec.ofNat 64 (base + 4104))))
  fls : t.globals.lookup gFls = some (.val (.word (BitVec.ofNat 64 (base + 4112))))
  fle : t.globals.lookup gFle = some (.val (.word (BitVec.ofNat 64 (base + 4120))))
  kb : t.globals.lookup gKb = some (.val (.word (BitVec.ofNat 64 (base + 8192))))
  ht : t.globals.lookup gHt = some (.val (.word (BitVec.ofNat 64 (base + H0 + 8 * NH))))
  eo : t.globals.lookup gEo = some (.val (.word 0))
  lit : t.globals.lookup gLit = some (.val (.word 0))
  et : t.globals.lookup gEt = some (.val (.word (BitVec.ofNat 64 (base + E0 + 8 * 64))))

/-! ## Memory facts beyond the stores -/

theorem Himg_length : Himg.length = NH := List.length_replicate ..

theorem Himg_get (i : Nat) (h : i < Himg.length) : Himg[i] = 0 := List.getElem_replicate ..

set_option hygiene false in
macro "addr_tac'" : tactic => `(tactic| (
    try simp only [Himg_length, NH, j0F, rbF, capF, capD, Lw, ENw, PO0, PO1, descAddr, layout, geoAt, w64, addr_add,
      base, T0, TW, M0, E0, H0, HNw, SZ, BitVec.ofNat_eq_ofNat] at *
    try simp (disch := omega) only [toNat_addr] at *
    try simp only [BitVec.toNat_ofNat] at *
    all_goals omega))

theorem tI_word {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (a : BitVec 64) (hal : a.toNat % 8 = 0)
    (h1 : base ≤ a.toNat) (h2 : a.toNat < base + SZ) : ∃ w, (tI t).memory a = .word w := by
  by_cases h : ∃ w, (a, w) ∈ initL
  · obtain ⟨w, hw⟩ := h; exact ⟨w, (tI_in hm a w hal h1 h2 hw).2⟩
  · refine ⟨0, (tI_out hm a hal h1 h2 (fun p hp e => h ⟨p.2, ?_⟩)).2⟩
    have : p.1 = a := BitVec.eq_of_toNat_eq e
    rw [← this]; exact hp

theorem clear_heap : ∀ p ∈ initL, p.1.toNat < base + H0 := by decide +kernel

theorem clear_env : ∀ i, i < 64 → i ≠ 55 → i ≠ 56 → ∀ p ∈ initL, p.1.toNat ≠ base + E0 + 8 * i := by
  decide +kernel

theorem memoR {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (code : Code) (r : Region) {K V : Type} [BEq K]
    [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V] (enc : K → List (BitVec 64)) (valW : V → BitVec 64) :
    MemoAtG enc valW (tI t) ((C0 code).mG r) ((C0 code).mg r) (∅ : Std.HashMap K V) := by
  have hi := rIdx_lt r
  simp only [C0, ctxOf, Nat.mod_eq_of_lt hi]
  exact memoAtG_empty _ _ _ _ _ (by simpa [w64] using descV_memo hm _ hi) (by simp [geoAt]) (by simp [geoAt])
    (emptyMem_memo hm _ hi)

theorem heapEx_init {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (code : Code) (hg : InitGlobals t code) :
    HeapEx (tI t) (C0 code).HB (C0 code).HN (C0 code).H := by
  refine ⟨Himg, List.prefix_refl _, ?_⟩
  simp only [C0, ctxOf]
  exact {
    top := by
      rw [show (tI t).globals = t.globals from rfl, hg.ht, Himg_length, addr_add]
    len := by rw [Himg_length]; simp [NH, j0F, rbF, capF, capD, Lw, HNw]
    lay := by addr_tac'
    dom := fun i hi => tI_dom hm _ (by addr_tac') (by addr_tac') (by addr_tac')
    val := fun i hi => by
      rw [Himg_get i hi]
      rw [Himg_length] at hi
      exact (tI_out hm _ (by addr_tac')
        (by addr_tac') (by addr_tac')
        (fun p hp e => by have := clear_heap p hp; rw [e] at this; addr_tac')).2
    words := fun i hi => tI_word hm _ (by addr_tac') (by addr_tac') (by addr_tac') }

theorem litW_P0 : litW (feStart P0) = 0 := by decide +kernel

theorem mem_env (i : Nat) (hi : i = 55 ∨ i = 56) :
    (w64 (base + E0 + 8 * i), EH0.getD i 0) ∈ initL := by
  unfold initL
  refine List.mem_append_right _ ?_
  rcases hi with rfl | rfl <;> simp [envL, EH0]

theorem EH0_length : EH0.length = 64 := by simp [EH0]

theorem envAt_init {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (code : Code) (hg : InitGlobals t code) :
    EnvAt (tI t) (C0 code) := by
  refine ⟨?_, memoR hm code .env _ _, memoR hm code .tbl _ _, ?_⟩
  · simp only [C0, ctxOf]
    exact {
      top := by rw [show (tI t).globals = t.globals from rfl, hg.et, EH0_length, addr_add]
      len := by rw [EH0_length]; simp [ENw]
      lay := by addr_tac'
      dom := fun i hi => tI_dom hm _ (by addr_tac') (by addr_tac') (by addr_tac')
      val := fun i hi => by
        rw [EH0_length] at hi
        by_cases h5 : i = 55 ∨ i = 56
        · have h := tI_in hm _ _ (by addr_tac') (by addr_tac') (by addr_tac') (mem_env i h5)
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [EH0_length]; omega)] at h
          simpa [w64, addr_add] using h.2
        · have h := (tI_out hm (BitVec.ofNat 64 (base + E0) + BitVec.ofNat 64 (8 * i)) (by addr_tac') (by addr_tac')
            (by addr_tac') (fun p hp e => clear_env i hi (by omega) (by omega) p hp (by rw [e]; addr_tac'))).2
          rw [h]; congr 1
          simp only [EH0, List.getElem_map, List.getElem_range]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      words := fun i hi => tI_word hm _ (by addr_tac') (by addr_tac') (by addr_tac') }
  · rw [show (tI t).globals = t.globals from rfl, hg.lit, show (C0 code).fe = feStart P0 from rfl, litW_P0]

theorem feStart_find (P : Pins) (n : NIdx) : (feStart P).find? n = none := by
  simp [feStart, IFEnv.find?, IFEnv.lookup, IFEnv.ofParts, IEnv.empty, IFBase.find?]

theorem feStart_findTable (P : Pins) (n : NIdx) : (feStart P).findTable? n = none := by
  simp [IFEnv.findTable?, feStart_find]

theorem envDen_init : EnvDen (feStart P0) P0 bootStore :=
  ⟨fun c ci h => absurd h (by simp [feStart_find]),
   fun T tb h => absurd h (by simp [feStart_findTable]),
   (boot_ok P0).2.2.2.1,
   fun c cv mI rP isK rules h => absurd h (by simp [feStart_find])⟩

theorem cachesOK_init : CachesOK (sBoot P0) :=
  ⟨fun k x h => by simp [sBoot, AState.init, Caches.empty] at h,
   fun k x h => by simp [sBoot, AState.init, Caches.empty] at h,
   fun k x h => by simp [sBoot, AState.init, Caches.empty] at h,
   fun k x h => by simp [sBoot, AState.init, Caches.empty] at h,
   fun k x h => by simp [sBoot, AState.init, Caches.empty] at h⟩

/-- **The invariant after the initial stores.** -/
theorem sr_init {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (code : Code) (hg : InitGlobals t code) :
    SR (C0 code) (sBoot P0) (tI t) where
  rep := srep_init hm
  gdir := hg.dir
  gfln := hg.fln
  gfll := hg.fll
  gfls := hg.fls
  gfle := hg.fle
  gkb := hg.kb
  code := hg.code
  kbuf j hj := tI_dom hm _ (by simp only [C0, ctxOf]; addr_tac') (by simp only [C0, ctxOf]; addr_tac')
    (by simp only [C0, ctxOf]; addr_tac')
  memo k := by cases k <;> exact memoR hm code _ _ _
  memoN k := by cases k <;> exact ⟨memoR hm code _ _ _, fun k v h => by simp [sBoot, AState.init, Memos.empty, memoSelN] at h⟩
  cache k := by cases k <;> first | trivial | exact memoR hm code _ _ _
  mode := ⟨by rw [show (tI t).globals = t.globals from rfl, hg.eo]; rfl,
    fun k => by cases k <;> first | trivial | exact memoR hm code _ _ _,
    fun k => by cases k <;> first | trivial | exact memoR hm code _ _ _⟩
  env := envAt_init hm code hg
  pins := rfl
  heap := heapEx_init hm code hg
  twf := (boot_ok P0).1.wf
  envd := envDen_init
  floor := Ext.refl _
  cok := cachesOK_init

theorem envRel_init (code : Code) : EnvRel (C0 code) :=
  ⟨fun n => by simp only [C0, ctxOf, feStart_find]; simp,
   fun n => by simp only [C0, ctxOf, feStart_findTable]; simp⟩

theorem pinsE_init (code : Code) : PinsE (C0 code) := by
  refine ⟨by simp [C0, ctxOf, P0, pinCount], fun i hi => ?_, ?_, ?_, ?_, ⟨by simp [C0, ctxOf, EH0, PO0, pinCount, w64,
    maxNatSizeDefault, P0, Pins.empty], by simp [C0, ctxOf, maxNatSizeDefault, P0, Pins.empty]⟩, ⟨w64 (base + E0 + 8 * 57), ?_, 57, ?_, ?_⟩⟩
  · have hi' : i < 52 := by simpa [C0, ctxOf, P0, pinCount] using hi
    simp only [C0, ctxOf, P0, PO0, Nat.zero_add, Array.getElem_replicate]
    simp [EH0, hi', show i < 64 by omega, show i ≠ 55 by omega, show i ≠ 56 by omega]; rfl
  · simp [C0, ctxOf, EH0, PO0, pinCount, P0, Pins.empty]; rfl
  · simp [C0, ctxOf, EH0, PO0, pinCount, P0, Pins.empty]; rfl
  · simp [C0, ctxOf, EH0, PO0, pinCount, P0, Pins.empty]; rfl
  · simp [C0, ctxOf, EH0, PO0, pinCount]
  · simp [C0, ctxOf, w64, addr_add]
  · simp [EBlk, C0, ctxOf, EH0, P0, Pins.empty]

theorem ctxOK_init (code : Code) : CtxOK (C0 code) :=
  ctxOK_ctxOf _ _ _ _ _ _ _ _ _ _ (envRel_init code) (pinsE_init code)

theorem frontOK_init (code : Code) : ConPanqueque.Front.FrontOK (C0 code) := frontOK_ctxOf _ _ _ _ _ _ _ _ _ _

end ConPanqueque.Start
