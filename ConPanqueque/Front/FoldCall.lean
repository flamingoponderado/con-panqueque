import ConPanqueque.Front.ToFold
import ConPanqueque.T.Floor

/-! # Calling the fold

`specR_callRet`: a call whose result is returned at once; only the twin's run matters after it, so
the callee's post can be anything. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.T.Decl

variable {σ : Type}

theorem specR_callRet {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM α}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop)
    (hB : ∀ u : PState σ, SR C s u →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf) :
    SpecR (Inv (σ := σ) C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) (.return (vv x))) s m
      (fun (_ : α) (_ : BitVec 64) (_ : AState) (_ : PState σ) => True) := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun _ _ t' => ∃ w, t'.locals.lookup x = some (.val (.word w)))
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) hcal)
    (fun u hu a w s' st _ => ⟨w, by simp only [setKvarHOLFinite]; exact lookup_setVar_same _ _ _⟩)
  rw [← bind_pure m]
  exact specR_bind (k := fun a => (pure a : AM α))
    (R := fun (_ : α) (_ : BitVec 64) (_ : AState) (_ : PState σ) => True) hc
    (fun a s' u ⟨w, hw⟩ => specR_return (P := (· = u)) (s := s') (a := a)
      (R := fun (_ : α) (_ : BitVec 64) (_ : AState) (_ : PState σ) => True) (vv x) (fun _ => w)
      (fun v hv => by subst hv; exact eval_vv _ x _ hw) (fun _ _ => trivial) u rfl) t rfl

def kN0 := ofString "kn0"

theorem declsRel_value {C : Ctx} {F rb capD : Nat} {H : List (BitVec 64)} {ds : Array IDeclaration}
    (h : DeclsRel C F rb capD H ds) : ∀ d ∈ ds.toList, ConPanqueque.Bridge.IsFrontDecl C.pins d := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨o, -, hr⟩ := h.2.2.2.2 k (by simpa using hk)
  simp only [Array.getElem_toList] at hr ⊢
  cases hx : ds[k] <;> rw [hx] at hr <;> first | trivial | exact hr.elim | exact hr.2.2.2.2 | exact hr.1

/-- After the parse: the record count, then the fold over the registry block. -/
def foldCallP : ProgHOL 64 :=
  .seq (.assign .local kN0 (.load .one (vv kRB)))
    (.seq (.call (some (some (.local, kR1), none)) fFold [vv kRB, .const 0, vv kN0]) (.return (vv kR1)))

set_option maxRecDepth 8000 in
theorem foldCodes_St {mode : ConLeche.CheckMode} {C : Ctx} (hc : FoldCodes mode C) (St : EStore) :
    FoldCodes mode (ctxSt C St) := by ctx_tr hc

theorem ILCodes.toSt {C : Ctx} (cc : ILCodes σ C) (St : EStore) : ILCodes σ (ctxSt C St) :=
  ⟨cc.nc, cc.sc, cc.ic, cc.cN, cc.cI, cc.cP, cc.cV, cc.rulesN, cc.ctorsN, cc.recsN, cc.typesN, cc.rulesAt, cc.ctorsAt,
    cc.recsAt, cc.typesAt, cc.declF, cc.typeF, cc.ctorF, cc.recF, cc.ruleF⟩

theorem frontCodes_St {C : Ctx} (h : FrontCodes σ C) (St : EStore) : FrontCodes σ (ctxSt C St) :=
  ⟨h.hsc, h.hnc, h.hhc, h.hlc, h.cNth, h.cSafe, h.cHintV, h.cStr, h.cApp, h.cLam, h.cAll, h.cLet, h.cProj, h.cLs, h.cConst, h.cBVar, h.cSort, h.cSucc, h.cParam, h.cMax, h.cImax, h.cNNum, h.cNStr, h.fApp, h.fLam, h.fAll, h.fLet, h.fProj, h.fConst, h.fNum, h.fStrN, h.fThm, h.fOpq, h.fAx, h.fQt, h.cQK, h.fDef, h.cLnPl, h.cLnS0, h.cLnIx, h.cLnNx, h.l1, h.l2, h.l3, h.l4, h.l5, h.l6, h.l7, h.l8, h.l9, h.l10, h.l11, h.l12, h.l14, h.l15, h.l16, h.l21, h.l22, h.l18, h.l19, h.cLnKB, h.ilc.toSt St, h.cCL, h.cRL, h.l23, h.cLitS, h.cQN, h.cRN, h.cLitW, h.cLitB, h.l13, h.l20, h.cMul, h.cAdd⟩

theorem declsRel_St {C : Ctx} {F rb capD : Nat} {H : List (BitVec 64)} {ds : Array IDeclaration}
    (h : DeclsRel C F rb capD H ds) (St : EStore) : DeclsRel (ctxSt C St) F rb capD H ds := by
  cases C; exact h

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

theorem foldCall_spec (pins : List INatOpPinSet) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hc : FoldCodes .verified C) (hfr : FrontOK C) (hs : C.side = false) (hpl : C.saved = none)
    (hfe : C.fe = feStart C.pins) (s : AState) (hA : denoteN s.store.ns default = some .anonymous) (Γ : Env) (D : List MlS) (hD : ∀ x ∈ [kN0, kR1], x ∈ D)
    (st : StateD) (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (hd : ∀ k (hk : k < st.decls.size), (denoteDecl s.store st.decls[k]).isSome)
    (hlen : st.decls.size < 2 ^ 62) (hRB : Γ.get kRB = some (cellA C rb))
    (hpo : ConRon.Bridge.PinsOK s) (hpp : ConRon.Bridge.PersPins s) (pinsP : List ConLeche.NatOpPinSet)
    (hpins : ConRon.Bridge.PinsDenote s.store pins pinsP) (hbi : BasisInv C) :
    SpecR (Inv (σ := σ) C s Γ [] D) foldCallP s (checkDeclsPure .verified pins st.decls.toList)
      (fun (_ : IFEnv) (_ : BitVec 64) (_ : AState) (_ : PState σ) => True) := by
  refine specR_atEntry fun t0 ht0 => ?_
  have hx0 : Ext C.St s.store := ht0.sr.floor
  refine specR_invRaise (R' := fun (_ : IFEnv) (_ : BitVec 64) (_ : AState) (_ : PState σ) => True) ?_
    (fun _ _ _ _ _ h => h)
  let C' := ctxSt C s.store
  obtain ⟨rs, hrs, hb, hrec⟩ := registry_block (C := ctxSt C s.store) (by ctx_tr hfr) hA (hbi.mono hx0)
    (declsRel_St hfs.dr s.store) hd
  have hrec' : ∀ j (hj : j < rs.length), RecOK C' rs[j].1 rs[j].2 := by
    intro j hj; have := hrec j hj; rwa [show ctxH (ctxSt C s.store) C.H = C' from by cases C; rfl] at this
  have hlenR : rs.length = st.decls.size := by
    have := congrArg List.length hrs; simpa using this
  have hdd0 : ∀ d ∈ rs.map Prod.snd, (∃ x, denoteDecl s.store d = some x) ∧ ConPanqueque.Bridge.IsFrontDecl C.pins d := by
    intro d hdm
    rw [hrs] at hdm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdm
    refine ⟨Option.isSome_iff_exists.mp (by simpa using hd k (by simpa using hk)), declsRel_value hfs.dr _ hdm⟩
  rw [← hrs]
  obtain ⟨h1, -, h3, h4, -⟩ := hfs.dr
  have hrbH : rb < C'.H.length := by show rb < C.H.length; omega
  refine specR_heapLoadI (C := C') kN0 (vv kRB) rb hrbH (hD _ (by simp))
    (by simp only [sev, vv]; rw [hRB]; rfl) ?_
  have hcnt : C'.H[rb] = BitVec.ofNat 64 rs.length := by
    rw [hlenR]; show C.H[rb] = _
    rw [List.getElem?_eq_getElem (by omega)] at h1; exact Option.some.inj h1
  refine specR_callRet (C := C') kR1 fFold foParams [vv kRB, .const 0, vv kN0] foldBody
    [cellA C' rb, BitVec.ofNat 64 0, BitVec.ofNat 64 rs.length] (by decide) rfl (hD _ (by simp))
    (foldCodes_St hc s.store).fold ?_ PostFold (fun u hu hlk t ht => ?_)
  · simp only [EvAll, sev, vv, Env.get_cons, ite_eq_right (show kRB ≠ kN0 by decide), ite_eq_left, hcnt]
    exact ⟨by rw [hRB]; rfl, rfl, trivial, trivial⟩
  · subst ht
    exact checkDeclsPure_spec .verified pins ra rs rb (by omega) C' s (ctxOK_St hok _) (foldCodes_St hc s.store)
      (by ctx_tr hfr) hA hs hpl hfe hu.pins hb hrec' rfl ⟨hu.twf⟩ hpo hpp pinsP hpins
      (fun j hj => by
        obtain ⟨hx, hf⟩ := hdd0 _ (List.mem_map_of_mem (f := Prod.snd) (List.getElem_mem hj))
        refine ⟨hx, ConPanqueque.Bridge.isChecked_of_front hpo ?_⟩
        rw [hu.pins]; exact hf) t ⟨hu, env_zip_get foParams _ rfl hlk⟩

end

end ConPanqueque.Front
