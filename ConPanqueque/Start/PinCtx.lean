import ConPanqueque.Start.PinList

/-! # After the pin phase: the real pin table

`C1 code H EH P`: the concrete layout with the real pin table `P` (block at `PO1` in the
environment heap) and the start environment of `P`.  `sr_switch`: once the twin installs `P`,
the invariant of the bootstrap family carries over to `C1`; `ctxOK_C1`: the layout facts, given
the pin block. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front

variable {σ : Type}

set_option maxRecDepth 100000

theorem litW_feStart (P : Pins) : litW (feStart P) = 0 := by
  have h : ConRon.Bridge.litsStoredOn ∅ { lits := List.map (fun i => P.names[i]!) strPins } 0 NAT_LIT_COUNT = false := by
    unfold ConRon.Bridge.litsStoredOn; rw [IFEnv.litsStored]
    simp [NAT_LIT_COUNT, strPins, IFEnv.find?, IFEnv.lookup, IFBase.find?]
  simp [litW, feStart, IFEnv.ofParts, IFEnv.natLitStoredBy, IFEnv.strLitStoredBy, boolW, h]

def namesOKb : List ConLeche.Name → List (List String) → Bool
  | [], [] => true
  | n :: ns, cs :: css => strComps n == some cs && cs.all (fun c => decide ((strBytes c).length < 2 ^ 50)) &&
      namesOKb ns css
  | _, _ => false

theorem namesOK_of : ∀ ns css, namesOKb ns css = true → NamesOK ns css
  | [], [], _ => trivial
  | n :: ns, cs :: css, h => by
    simp only [namesOKb, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, fun c hc => h.1.2 c hc, namesOK_of ns css h.2⟩
  | [], _ :: _, h => by simp [namesOKb] at h
  | _ :: _, [], h => by simp [namesOKb] at h

def pinCss : List (List String) := pinNames.map fun n => (strComps n).getD []
def resCss : List (List String) := reservedBasisNameValues.map fun n => (strComps n).getD []

theorem pinCss_ok : NamesOK pinNames pinCss := namesOK_of _ _ (by decide +kernel)
theorem resCss_ok : NamesOK reservedBasisNameValues resCss := namesOK_of _ _ (by decide +kernel)

theorem pinNames_length : pinNames.length = 52 := by decide
theorem reserved_length : reservedBasisNameValues.length = 16 := by decide

theorem internNameList_length : ∀ (ns : List ConLeche.Name) (s s' : AState) (hs : List NIdx),
    internNameList ns s = .ok (hs, s') → hs.length = ns.length
  | [], s, s', hs, h => by
    simp [internNameList, pure, StateT.pure, Except.pure] at h; rw [h.1]; rfl
  | n :: ns, s, s', hs, h => by
    simp only [internNameList, bind, StateT.bind, Except.bind] at h
    cases h1 : internName n s with
    | error e => rw [h1] at h; cases h
    | ok r =>
      obtain ⟨a, s1⟩ := r
      rw [h1] at h; simp only at h
      cases h2 : internNameList ns s1 with
      | error e => rw [h2] at h; cases h
      | ok r2 =>
        obtain ⟨as, s2⟩ := r2
        rw [h2] at h; simp [pure, StateT.pure, Except.pure] at h
        rw [← h.1]; simp [internNameList_length ns s1 s2 as h2]

/-- The context once the pins are in. -/
def C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) : Ctx :=
  ctxOf code H none bootStore (feStart P) EH ∅ ∅ P PO1

theorem C1_EH (code : Code) (H EH : List (BitVec 64)) (P : Pins) : (C1 code H EH P).EH = EH := rfl

/-- **The pin table switch**: the twin's `set` of the pins, with the memory as it is. -/
theorem sr_switch {code : Code} {H EH : List (BitVec 64)} {sX : AState} {t : PState σ} (P : Pins)
    (h : SR (Cb code H EH) sX t) (hz : denoteL sX.store.ls P.zeroLevel = some .zero) :
    SR (C1 code H EH P) { sX with pins := P } t where
  rep := h.rep
  gdir := h.gdir
  gfln := h.gfln
  gfll := h.gfll
  gfls := h.gfls
  gfle := h.gfle
  gkb := h.gkb
  code := h.code
  kbuf := h.kbuf
  memo := h.memo
  memoN := h.memoN
  cache := h.cache
  mode := h.mode
  env := by
    obtain ⟨hH, hm1, hm2, hl⟩ := h.env
    refine ⟨hH, hm1, hm2, ?_⟩
    rw [hl]
    show some (ValueHOL.val (HolWordLab.word (litW (feStart P0)))) = some (ValueHOL.val (HolWordLab.word (litW (feStart P))))
    rw [litW_feStart, litW_feStart]
  pins := rfl
  heap := h.heap
  twf := h.twf
  envd := ⟨fun c ci hc => absurd hc (by simp [C1, ctxOf, feStart_find]),
    fun T tb hT => absurd hT (by simp [C1, ctxOf, feStart_findTable]), hz,
    fun c cv mI rP isK rules hc => absurd hc (by simp [C1, ctxOf, feStart_find])⟩
  floor := h.floor
  cok := cachesOK_congr h.cok rfl ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem envRel_C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) : EnvRel (C1 code H EH P) :=
  ⟨fun n => by simp only [C1, ctxOf, feStart_find]; simp,
   fun n => by simp only [C1, ctxOf, feStart_findTable]; simp⟩

/-- The pin block at `PO1 = 64`, the reserved names' block at `121`. -/
structure PinBlock (EH : List (BitVec 64)) (P : Pins) : Prop where
  size : P.names.size = pinCount
  names : ∀ i (hi : i < P.names.size), EH[64 + i]? = some (Enc.idxW P.names[i])
  us : EH[64 + 52]? = some (Enc.idxW P.emptyLevels)
  z : EH[64 + 53]? = some (Enc.idxW P.zeroLevel)
  s1 : EH[64 + 54]? = some (Enc.idxW P.sortOne)
  mx : EH[64 + 55]? = some (BitVec.ofNat 64 maxNatSizeDefault) ∧ P.maxNatSize = maxNatSizeDefault
  ptr : EH[64 + 56]? = some (BitVec.ofNat 64 (base + E0) + BitVec.ofNat 64 (8 * 121))
  cnt : EH[121]? = some (BitVec.ofNat 64 P.reserved.length)
  res : ∀ i (hi : i < P.reserved.length), EH[122 + i]? = some (Enc.idxW P.reserved[i])

theorem pinsE_C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) (hb : PinBlock EH P) :
    PinsE (C1 code H EH P) := by
  refine ⟨hb.size, fun i hi => ?_, hb.us, hb.z, hb.s1, ⟨by simp only [C1, ctxOf]; rw [hb.mx.2]; exact hb.mx.1, by
    simp only [C1, ctxOf]; rw [hb.mx.2]; simp [maxNatSizeDefault]⟩, ⟨_, hb.ptr, 121, rfl, ?_, fun i hi => ?_⟩⟩
  · exact hb.names i hi
  · simp only [C1, ctxOf, List.length_map]; exact hb.cnt
  · simp only [List.length_map] at hi
    simp only [C1, ctxOf, List.getElem_map]
    rw [show 121 + 1 + i = 122 + i by omega]; exact hb.res i hi

theorem ctxOK_C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) (hb : PinBlock EH P) :
    CtxOK (C1 code H EH P) :=
  ctxOK_ctxOf _ _ _ _ _ _ _ _ _ _ (envRel_C1 code H EH P) (pinsE_C1 code H EH P hb)

theorem frontOK_C1 (code : Code) (H EH : List (BitVec 64)) (P : Pins) : FrontOK (C1 code H EH P) :=
  frontOK_ctxOf _ _ _ _ _ _ _ _ _ _

/-- A call whose callee's post is `w = enc a ∧ SR (ctxH C Hp) s' st`. -/
theorem specR_callPost {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs) (enc : α → BitVec 64) (Hp : List (BitVec 64))
    (hB : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s m (fun a w s' st => w = enc a ∧ SR (ctxH C Hp) s' st))
    (hk : ∀ a s', m s = .ok (a, s') → SpecR (Inv (ctxH C Hp) s' ((x, enc a) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIA x f ps es B vs hnd hl hx hC hes
    (fun a w s' st => m s = .ok (a, s') ∧ w = enc a ∧ SR (ctxH C Hp) s' st)
    (fun a w s' H' => H' = Hp ∧ m s = .ok (a, s') ∧ w = enc a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨Hp, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by subst hw'; exact hB _ (pre_of_lookups hu ps vs hl hlk)))
    (fun a w s' H' ⟨e, hr, hw⟩ => by subst e; subst hw; exact hk a s' hr)

end ConPanqueque.Start
