import ConPanqueque.T.Decl.IdxInsRec
import ConPanqueque.T.Core.ReduceProj

/-!
# Installing a projection table

`fe.pushTable t`: the table's record is in the environment heap, its structure's name goes into the table
memo (`tblM`), and the context becomes `ctxTb C fe' EH (C.tblM.insert …)`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T

theorem find?_pushTable (fe : IFEnv) (t : IProjTable) (n : NIdx) : (fe.pushTable t).find? n = fe.find? n := by
  rw [IFEnv.find?_eq, IFEnv.find?_eq]; rfl

theorem rawTable?_pushTable (fe : IFEnv) (t : IProjTable) (n : NIdx) :
    (fe.pushTable t).rawTable? n = if (t.structName == n) = true then some t else fe.rawTable? n := by
  unfold IFEnv.rawTable? IFEnv.pushTable
  simp only [Std.HashMap.getElem?_insert]
  by_cases h : (t.structName == n) = true <;> simp [h]

theorem findTable?_pushTable (fe : IFEnv) (t : IProjTable) (hs : (fe.find? t.structName).isSome = true) (n : NIdx) :
    (fe.pushTable t).findTable? n = if (t.structName == n) = true then some t else fe.findTable? n := by
  unfold IFEnv.findTable?
  rw [find?_pushTable, rawTable?_pushTable]
  by_cases h : (t.structName == n) = true
  · have : t.structName = n := by simpa using h
    subst this; simp [hs]
  · simp [h]

/-- The context with environment `fe`, image `EH` and table memo `tblM`. -/
def ctxTb (C : Ctx) (fe : IFEnv) (EH : List (BitVec 64)) (tblM : Std.HashMap NIdx (BitVec 64)) : Ctx :=
  { C with fe := fe, EH := EH, tblM := tblM }

theorem envRel_tb {C : Ctx} (h : EnvRel C) {fe : IFEnv} {EH : List (BitVec 64)} {t : IProjTable} {o : Nat}
    (hp : C.EH <+: EH) (htb : TblE C.EB EH o t) (hf : ∀ n, fe.find? n = C.fe.find? n)
    (ht : ∀ n, fe.findTable? n = if (t.structName == n) = true then some t else C.fe.findTable? n) :
    EnvRel (ctxTb C fe EH (C.tblM.insert t.structName (ecell C o))) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · show match fe.find? n with
      | none => C.envM[n]? = none
      | some ci => ∃ o', C.envM[n]? = some (ecell C o') ∧ CIE C.EB EH o' ci
    rw [hf]
    have := h.1 n
    revert this
    cases C.fe.find? n with
    | none => exact id
    | some ci => exact fun ⟨o', hm, hc⟩ => ⟨o', hm, cie_mono hp hc⟩
  · show match fe.findTable? n with
      | none => (C.tblM.insert t.structName (ecell C o))[n]? = none
      | some tb => ∃ o', (C.tblM.insert t.structName (ecell C o))[n]? = some (ecell C o') ∧ TblE C.EB EH o' tb
    rw [ht, Std.HashMap.getElem?_insert]
    by_cases e : (t.structName == n) = true
    · simp only [e, ite_true]; exact ⟨o, rfl, htb⟩
    · have ef : (t.structName == n) = false := by simpa using e
      simp only [ef, Bool.false_eq_true, ite_false]
      have := h.2 n
      revert this
      cases C.fe.findTable? n with
      | none => exact id
      | some tb => exact fun ⟨o', hm, hc⟩ => ⟨o', hm, tblE_mono hp hc⟩

theorem ctxOK_tb {C : Ctx} (hok : CtxOK C) {fe : IFEnv} {EH : List (BitVec 64)} {t : IProjTable} {o : Nat}
    (hp : C.EH <+: EH) (htb : TblE C.EB EH o t) (hf : ∀ n, fe.find? n = C.fe.find? n)
    (ht : ∀ n, fe.findTable? n = if (t.structName == n) = true then some t else C.fe.findTable? n) :
    CtxOK (ctxTb C fe EH (C.tblM.insert t.structName (ecell C o))) := by
  have h1 := envRel_tb hok.envRel hp htb hf ht
  have h2 : PinsE (ctxTb C fe EH (C.tblM.insert t.structName (ecell C o))) := pinsE_E hok.pinsRel hp
  cases hok; constructor <;> first | assumption | exact h1 | exact h2

section
variable {σ : Type}

/-- Rebuilding `SR` after a write confined to the table memo's region. -/
theorem sr_tbIns {C : Ctx} {EH : List (BitVec 64)} (hok : CtxOK (ctxE C EH)) {s : AState} {t u : PState σ}
    (hsr : SR (ctxE C EH) s t) (hfr : ∀ c, ¬ inR (C.mg .tbl) c → u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals = t.globals) (hc : u.code = t.code)
    {fe : IFEnv} {tblM : Std.HashMap NIdx (BitVec 64)}
    (hm : MemoAtG encNI id u (C.mG .tbl) (C.mg .tbl) tblM) (hlit : litW fe = litW C.fe)
    (hden : EnvDen fe C.pins s.store) :
    SR (ctxTb C fe EH tblM) s u := by
  obtain ⟨hH, hm1, _, hl⟩ := hsr.env
  refine ⟨srep_frame hsr.rep ⟨hfr _ (hok.flMemo .tbl _ (Or.inl rfl)), hfr _ (hok.flMemo .tbl _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo .tbl _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo .tbl _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo .tbl kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut .tbl c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd]; exact hsr.kbuf j hj,
    fun k => memoAt_frame (hsr.memo k) (fun c hc => hfr c (hok.memoDis (.e k) .tbl c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .tbl (.e k) kk hkk)) hd,
    fun k => memoAtN_frame (hsr.memoN k) (fun c hc => hfr c (hok.memoDis (.n k) .tbl c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .tbl (.n k) kk hkk)) hd,
    fun k => cacheAt_frame (hsr.cache k) (fun c hc => hfr c (hok.memoDis (.c k) .tbl c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .tbl (.c k) kk hkk)) hd,
    modeAt_frame hsr.mode (fun b k c hc => hfr c (hok.memoDis (.m b k) .tbl c (by simp) hc))
      (fun b k kk hkk => hfr _ (hok.mdescMemo .tbl (.m b k) kk hkk)) hd (by rw [hg]),
    ⟨⟨by rw [hg]; exact hH.top, hH.len, hH.lay, fun i hi => by rw [hd]; exact hH.dom i hi,
        fun i hi => by
          have e := hfr _ (hok.envMemo .tbl i (Nat.lt_of_lt_of_le hi hH.len)); unfold ecell at e
          exact e.trans (hH.val i hi),
        fun i hi => by
          have e := hfr _ (hok.envMemo .tbl i hi); unfold ecell at e
          exact (hH.words i hi).imp fun w hw => e.trans hw⟩,
      memoAtG_frame hm1 (fun c hc => hfr c (hok.memoDis .env .tbl c (by decide) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .tbl .env kk hkk)) hd, hm,
      by rw [hg, show (ctxTb C fe EH tblM).fe = fe from rfl, hlit]; exact hl⟩, hsr.pins,
    heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo .tbl i hi)) hd (by rw [hg]), hsr.twf, hden, hsr.floor, hsr.cok⟩

end

/-- The table memo's insert of the structure's name (the table's record already in the environment heap). -/
def tbInsP (C : Ctx) (eN eX : ExpHOL 64) (r : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eN)
  (.seq (.call (some (some (.local, r), none)) fMemoSet [.const (C.mG .tbl), .const 1, eX]) rest)

/-- The denotation facts `TblDen` asks of one table. -/
def NewTblDen (t : IProjTable) (st : EStore) : Prop :=
  (∀ n ∈ t.levelParams, (denoteN st.ns n).isSome = true) ∧ (∀ b ∈ t.bodies.toList, (denoteE st b).isSome = true) ∧
    t.levelParams.length + 1 < 2 ^ 60 ∧ t.bodies.size = t.numFields

theorem envDen_pushTable {fe : IFEnv} {p : Pins} {st : EStore} {t : IProjTable}
    (hs : (fe.find? t.structName).isSome = true) (h : EnvDen fe p st) (hnew : NewTblDen t st) :
    EnvDen (fe.pushTable t) p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  refine ⟨fun c ci hci => hc c ci (by rw [← find?_pushTable fe t]; exact hci), fun T tbl h' => ?_, hp,
    fun c cv mI rP isK rules hci => hr c cv mI rP isK rules (by rw [← find?_pushTable fe t]; exact hci)⟩
  rw [findTable?_pushTable fe t hs] at h'
  split at h'
  · cases h'; exact hnew
  · exact htb T tbl h'

section
variable {σ : Type}

theorem specR_tbInsI {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (t : IProjTable) (hs : (C.fe.find? t.structName).isSome = true)
    (EH : List (BitVec 64)) (ox : Nat) (hpE : C.EH <+: EH) {s : AState} (hden : NewTblDen t s.store)
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (eN eX : ExpHOL 64) (r : MlS) (hr : r ∈ D) (heN : sev Γ eN = some (Enc.idxW t.structName))
    (heX' : sev Γ eX = some (ecell C ox)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv (ctxTb C (C.fe.pushTable t) EH (C.tblM.insert t.structName (ecell C ox))) s ((r, w) :: Γ)
      [] D) rest s m R) :
    SpecR (Inv (ctxE C EH) s Γ M D) (tbInsP C eN eX r rest) s m R := by
  unfold tbInsP
  refine specR_storeKBI (ctxOK_E hok hpE) 0 (by decide) eN (Enc.idxW t.structName) heN hkb ?_
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => m) (by simp) ?_
  refine specR_memoSetGIC (C := ctxE C EH)
    (C' := ctxTb C (C.fe.pushTable t) EH (C.tblM.insert t.structName (ecell C ox)))
    (D := D) (K := NIdx) (V := BitVec 64) encNI_inj (C.mG .tbl) (C.mg .tbl) C.tblM t.structName (ecell C ox) (pure ()) rfl
    (fun u hu => hu.env.2.2.1) (fun i hi => hok.kbMemo .tbl i (by simp [encNI] at hi; omega))
    (fun j hj => hok.mdescMemo .tbl .tbl j hj)
    (fun u u' hsr hmem hfr hd hg' hc => sr_tbIns (ctxOK_E hok hpE) hsr hfr hd hg' hc hmem rfl
      (envDen_pushTable hs hsr.envd hden))
    hcS hcI r (.const (C.mG .tbl)) (.const 1) eX hr rfl rfl heX'
    (by simp [encNI]) (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW t.structName) (by simp)) (fun w => ?_)
  exact hk w

end

end ConPanqueque.T.Decl
