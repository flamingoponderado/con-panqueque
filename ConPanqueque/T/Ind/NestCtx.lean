import ConPanqueque.T.Ind.SumCtor
import ConPanqueque.T.Ind.PiTele
import ConPanqueque.T.Ind.DropVars
import ConRon.Arena.Inductives.BlockInstall
import ConPanqueque.T.Core.UnitLikeFields

/-!
# The positivity walk's context (`blockNestCtx`)

`ipBody`: `instPisWith (args.drop i) e`, hanging at `none` (its one caller fails there).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def ipwA := ofString "ipw_a"
def ipwI := ofString "ipw_i"
def ipwN := ofString "ipw_n"
def ipwE := ofString "ipw_e"
def ipwX := ofString "ipw_x"
def ipwR := ofString "ipw_r"
def fInstPis := ofString "instPisWith"

def ipwParams : List MlS := [ipwA, ipwI, ipwN, ipwE]
def ipwLocals : List MlS := gaaLocals ++ [ipwX, ipwR]

def ipwBody : ProgHOL 64 := prologue ipwLocals
  (.ite (.cmp .lower (vv ipwI) (vv ipwN))
    (.ite (tagIsE ipwE 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ipwE)) (.seq eViewP
      (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local ipwX (.load .one (.op .add [vv ipwA, .op .add [.panop .mul [vv ipwI, .const 8], .const 8]])))
      (.seq (.call (some (some (.local, ExS.lY), none)) fInst1F [.const (BitVec.ofNat 64 coreWalkFuel), vv lA2, vv ipwX, .const 0])
      (.seq (.call (some (some (.local, ipwR), none)) fInstPis [vv ipwA, .op .add [vv ipwI, .const 1], vv ipwN, vv ExS.lY])
        (.return (vv ipwR)))))))))
      hang)
    (.return (vv ipwE)))

section
variable {σ : Type}

theorem ipw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ipwLocals → (ctxEnv C ++ ipwParams.zip vals).get x = none :=
  Knot.params_none C ipwLocals ipwParams vals (by decide) (by decide)

/-- An `Option` handle that is `some`, as its word. -/
def PostSome (C : Ctx) (o : Option EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ t, o = some t ∧ w = Enc.idxW t ∧ SR C s' st

theorem postSome_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSome C a w s' st → PostSome C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨t, h1, h2, h3⟩ => ⟨t, h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

/-- **`instPisWith`** from position `i`. -/
theorem ipw_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcI : Codes C (ExI.body C)) (args : List EIdx) (pa : Nat) (H : List (BitVec 64)) (hA : BlkAt H pa (args.map Enc.idxW)) :
    ∀ f i (s : AState) (e : EIdx), args.length - i = f → i ≤ args.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ipwParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 args.length,
        Enc.idxW e])) ipwBody s (instPisWith (args.drop i) e) (PostSome (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s e hf hi
    have hin : i = args.length := by omega
    subst hin
    refine specR_prologue (postSome_locals _) (ipw_none _ _) ?_
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff args.length args.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ipwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, instPisWith]
    exact specR_returnI _ _ (by simp +decide [sev, Env.get, ipwParams, ctxEnv])
      (fun t ht => ⟨e, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s e hf hi
    have hin : i < args.length := by omega
    refine specR_prologue (postSome_locals _) (ipw_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hal := blkAt_len_le hA
    simp only [List.length_map] at hal
    have hlw := nd_lt_iff i args.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ipwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, instPisWith]
    obtain ⟨w, hw, hiff⟩ := sev_tagIs (ctxEnv (ctxH C H) ++ ipwParams.zip [cellA C pa, BitVec.ofNat 64 i,
      BitVec.ofNat 64 args.length, Enc.idxW e]) ipwE e (by simp +decide [Env.get, ipwParams, ctxEnv]) 6 (by omega) (by omega)
    by_cases ht : e.tag = UInt32.ofNat 6
    case neg =>
      exact specR_ifI _ w hw (fun e' => absurd (hiff.mp e') ht) (fun _ => specR_hangI)
    have hb : (e.tag == ETag.forallE) = true := by simp [ht]; rfl
    rw [hb]; simp only [ite_true]
    refine specR_ifI _ w hw (fun _ => ?_) (fun e' => absurd (hiff.mpr ht) (by simp [e']))
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ipwParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ipwE) (Enc.idxW e) (by decide) (by simp +decide [Env.get_cons, Env.get, ipwParams, ctxEnv]) ?_
    refine specR_viewXI ConRon.Arena.viewBind projBind e (fun vw hvw => viewBind_run e (Or.inr ht) s vw hvw)
      (by simp) (by simp +decide <;> rfl) (by simp +decide [Env.get_cons, Env.get, ipwParams, ctxEnv] <;> rfl) (by decide)
      (fun vw P htg hsh => ?_)
    obtain ⟨ty, b, hpb, hwv⟩ : ∃ ty b, projBind vw = some (ty, b) ∧ encEView vw = [Enc.idxW ty, Enc.idxW b] := by
      have htT : e.tag.toNat = 6 := by rw [ht]; simp
      rw [htT] at htg
      cases vw with
      | lam ty b => exact ⟨ty, b, rfl, rfl⟩
      | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
      | _ => simp [ENodeView.tagN] at htg <;> omega
    rw [hpb]; simp only
    refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by rw [hwv]; exact wordsAt_mem1 _ _ _ _ _) ?_
    have hx := hA.2 i (by simp; omega)
    simp only [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) ipwX _ (pa + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, ipwParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine ILP.callE_spec (C := ctxH C H) ExS.lY fInst1F [pFu, pH, pV, pD]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv lA2, vv ipwX, .const 0]
      (fastBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW args[i], BitVec.ofNat 64 0] (by decide) rfl
      (by decide) hcF ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (fast_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hcI) s coreWalkFuel b args[i] 0 (by decide) (by decide))
      (fun e1 s1 => ?_)
    refine specR_congr (m' := instPisWith (args.drop (i + 1)) e1 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIM ipwR fInstPis ipwParams [vv ipwA, .op .add [vv ipwI, .const 1], vv ipwN, vv ExS.lY] ipwBody
      [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 args.length, Enc.idxW e1] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ipwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ipwParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, ipwParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSome (ctxH C H)) (fun _ _ _ _ ⟨_, _, _, h⟩ => h)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipwParams _ rfl hlk) (ih (i + 1) s1 e1 (by omega) (by omega)))
      (fun r w s2 st ⟨t, hrt, hwt, _⟩ => ?_)
    subst hwt
    exact specR_returnI _ _ (by simp [Env.get]) (fun t' ht' => ⟨t, hrt, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)

end

/-! ## `nestHoles` -/

def nhM := ofString "nh_m"
def nhQ := ofString "nh_q"
def nhP := ofString "nh_p"
def nhW := ofString "nh_w"
def nhI := ofString "nh_i"
def nhN := ofString "nh_n"
def nhMp := ofString "nh_mp"
def nhCv := ofString "nh_cv"
def nhTy := ofString "nh_ty"
def nhK := ofString "nh_k"
def nhT := ofString "nh_t"
def nhV := ofString "nh_v"
def fNestHoles := ofString "nestHolesFill"

def nhParams : List MlS := [nhM, nhQ, nhP, nhW, nhI, nhN]
def nhLocals : List MlS := [nhMp, nhCv, nhTy, nhK, nhT, nhV]

def nhBody : ProgHOL 64 := prologue nhLocals
  (.ite (.cmp .lower (vv nhI) (vv nhN))
    (.seq (.assign .local nhMp (.load .one (.op .add [vv nhM, .op .add [.panop .mul [vv nhI, .const 8], .const 8]])))
    (.seq (.assign .local nhCv (.load .one (vv nhMp)))
    (.seq (.assign .local nhTy (.load .one (.op .add [vv nhCv, .const 16])))
    (.seq (.assign .local nhK (.load .one (vv nhQ)))
    (.seq (.call (some (some (.local, nhT), none)) fInstPis [vv nhQ, .const 0, vv nhK, vv nhTy])
    (.seq (.call (some (some (.local, nhV), none)) fInternFVar [vv nhT, .op .add [vv nhP, vv nhI]])
    (.seq (.store (.op .add [vv nhW, .panop .mul [vv nhI, .const 8]]) (vv nhV))
    (.seq (.call (some (some (.local, nhV), none)) fNestHoles
        [vv nhM, vv nhQ, vv nhP, vv nhW, .op .add [vv nhI, .const 1], vv nhN])
      (.return (.const 0))))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem nh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nhLocals → (ctxEnv C ++ nhParams.zip vals).get x = none :=
  Knot.params_none C nhLocals nhParams vals (by decide) (by decide)

/-- The fill's post: the twin's answer is `some (out ++ ys)`, `ys` written from `ow + i`. -/
def PostNH (C : Ctx) (H0 : List (BitVec 64)) (len ow i n : Nat) (out : List EIdx) (o : Option (List EIdx))
    (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', H0 <+: H' ∧ H'.length = len ∧ SR (ctxH C H') s' st ∧ ∃ ys, o = some (out ++ ys) ∧ ys.length = n - i ∧
    ∀ j (hj : j < ys.length), H'[ow + i + j]? = some (Enc.idxW ys[j])

theorem postNH_locals (C : Ctx) (H0 : List (BitVec 64)) (len ow i n : Nat) (out : List EIdx) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostNH C H0 len ow i n out a w s' st →
      PostNH C H0 len ow i n out a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hl, hs, h1⟩ => ⟨H', hp, hl, sr_of_eq hs rfl rfl rfl rfl, h1⟩

/-- **`nestHoles`**' loop from member `i`. -/
theorem nh_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fNestHoles = some (nhParams.map (fun p => (p, ShapeHOL.one)), nhBody, .one))
    (hcP : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcI : Codes C (ExI.body C))
    (hcV : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    (ctx : NestCtx) (ms : List MemberShape) (hf : ctx.formers = ms.map (·.cvT)) (hnl : ctx.names.length = ms.length)
    (om pq ow : Nat) (H0 : List (BitVec 64)) (hM : PtrsRep C H0 om (MemberRep C H0) ms)
    (hQ : BlkAt H0 pq (ctx.params.map Enc.idxW)) (hnP : ctx.nP + ms.length < 2 ^ 62) (hml : ms.length < 2 ^ 59) :
    ∀ f i (Hb H : List (BitVec 64)) (s : AState) (out : List EIdx), ms.length - i = f → i ≤ ms.length → H0 <+: Hb →
      Hb <+: H → Hb.length ≤ ow + i → ow + ms.length ≤ H.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (nhParams.zip [cellA C om, cellA C pq, BitVec.ofNat 64 ctx.nP, cellA C ow,
        BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length])) nhBody s (nestHoles.go ctx i (ctx.names.drop i) out)
        (PostNH C Hb H.length ow i ms.length out) := by
  intro f
  induction f with
  | zero =>
    intro i Hb H s out hf' hi hb0 h0 hl0 hroom
    have hin : i = ms.length := by omega
    subst hin
    refine specR_prologue (postNH_locals _ _ _ _ _ _ _) (nh_none _ _) ?_
    have hlw := nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, nhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [← hnl, List.drop_length, nestHoles.go]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, h0, rfl, sr_of_eq ht.sr rfl rfl rfl rfl, [], by simp, by simp,
      fun j hj => absurd hj (by simp)⟩)
  | succ f ih =>
    intro i Hb H s out hf' hi hb0 h0 hl0 hroom
    have hin : i < ms.length := by omega
    refine specR_prologue (postNH_locals _ _ _ _ _ _ _) (nh_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, nhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (show i < ctx.names.length by omega), nestHoles.go]
    have hfi : ctx.formers[i]? = some ms[i].cvT := by rw [hf]; simp [hin]
    rw [hfi]; simp only
    obtain ⟨omi, hmi, hrep⟩ := hM.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -⟩ := hrep
    obtain ⟨-, -, hty⟩ := hcv
    refine UD.specR_heapLoadI' (C := ctxH C H) nhMp _ (om + 1 + i) _ (get_prefix hmi (hb0.trans h0)) (by decide)
      (by simp +decide [sev, Env.get, nhParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nhCv (vv nhMp) omi _ (get_prefix hoc (hb0.trans h0)) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nhTy _ (oc + 2) _ (get_prefix hty (hb0.trans h0)) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nhK (vv nhQ) pq _ (get_prefix hQ.1 (hb0.trans h0)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv]; rfl) ?_
    have hpe : instPisWith ctx.params ms[i].cvT.type = instPisWith (ctx.params.drop 0) ms[i].cvT.type := by simp
    rw [hpe]
    refine specR_callNIM nhT fInstPis ipwParams [vv nhQ, .const 0, vv nhK, vv nhTy] ipwBody
      [cellA C pq, BitVec.ofNat 64 0, BitVec.ofNat 64 (List.map Enc.idxW ctx.params).length, Enc.idxW ms[i].cvT.type]
      (by decide) rfl (by decide) hcP
      ⟨by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSome (ctxH C H)) (fun _ _ _ _ ⟨_, _, _, h⟩ => h)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipwParams _ rfl hlk) (by
        have := ipw_spec (σ := σ) ra C hok hcP hcF hcI ctx.params pq H (blkAt_mono hQ (hb0.trans h0)) _ 0 s ms[i].cvT.type rfl (by omega)
        simpa only [List.length_map] using this))
      (fun o w s1 st ⟨t, hot, hwt, _⟩ => ?_)
    subst hot; subst hwt
    simp only
    refine specR_internFVarR ra (ctxOK_H hok H) hcV nhV (vv nhT) (.op .add [vv nhP, vv nhI]) t (ctx.nP + i) (by omega)
      (by decide) (by simp +decide [sev, Env.get_cons])
      (by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat]) (fun h s2 _ => ?_)
    let Γ0 : Env := ctxEnv (ctxH C H) ++ nhParams.zip [cellA C om, cellA C pq, BitVec.ofNat 64 ctx.nP, cellA C ow,
      BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length]
    refine specR_heapStoreI (ctxOK_H hok H) (.op .add [vv nhW, .panop .mul [vv nhI, .const 8]]) (vv nhV) (ow + i)
      (by show _ < H.length; omega) (Enc.idxW h)
      (by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv]; exact cellA_mulOff C ow i (by omega))
      (by simp [sev, Env.get_cons]) ?_
    let H2 := H.set (ow + i) (Enc.idxW h)
    have hl2 : H2.length = H.length := by simp [H2]
    have h02 : Hb <+: H2 := prefix_set h0 hl0 _
    let H0' := H2.take (ow + i + 1)
    have h00' : Hb <+: H0' := prefix_take_of h02 (by omega)
    have h0'2 : H0' <+: H2 := List.take_prefix _ _
    have hcell : H0'[ow + i]? = some (Enc.idxW h) := by
      simp only [H0', H2, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by omega)
    refine specR_congr (m' := nestHoles.go ctx (i + 1) (ctx.names.drop (i + 1)) (out ++ [h]) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIG (C := ctxH (ctxH C H) H2) nhV fNestHoles nhParams
      [vv nhM, vv nhQ, vv nhP, vv nhW, .op .add [vv nhI, .const 1], vv nhN] nhBody
      [cellA C om, cellA C pq, BitVec.ofNat 64 ctx.nP, cellA C ow, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length]
      (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, nhParams, ctxEnv], trivial⟩
      (PostNH C H0' H2.length ow (i + 1) ms.length (out ++ [h])) (fun o _ _ H' => H0' <+: H' ∧ H'.length = H2.length ∧
        ∃ ys, o = some (out ++ [h] ++ ys) ∧ ys.length = ms.length - (i + 1) ∧
          ∀ j (hj : j < ys.length), H'[ow + (i + 1) + j]? = some (Enc.idxW ys[j]))
      (fun o w s' st ⟨H', hp', hl', hs', h1⟩ => ⟨H', ⟨hp', hl', h1⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nhParams _ rfl hlk)
        (ih (i + 1) H0' H2 s2 (out ++ [h]) (by omega) (by omega) (hb0.trans h00') h0'2 (by simp [H0', hl2]; omega) (by omega)))
      (fun o w s3 H4 ⟨h0'4, hl4, ys, hys, hyl, hcells⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, h00'.trans h0'4, by rw [hl4, hl2], sr_of_eq ht.sr rfl rfl rfl rfl,
      h :: ys, by rw [hys]; simp, by simp; omega, fun j hj => by
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        exact get_prefix hcell h0'4
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [show ow + i + (j + 1) = ow + (i + 1) + j by omega]
        exact hcells j (by simpa using hj)⟩)

end

/-! ## `blockNestCtx` -/

def bnM := ofString "bn_m"
def bnP := ofString "bn_p"
def bnK := ofString "bn_k"
def bnM0 := ofString "bn_m0"
def bnCv := ofString "bn_cv"
def bnTy := ofString "bn_ty"
def bnQ := ofString "bn_q"
def bnPq := ofString "bn_pq"
def bnL := ofString "bn_l"
def bnU := ofString "bn_u"
def bnY := ofString "bn_y"
def bnX := ofString "bn_x"
def bnR := ofString "bn_r"
def fBlockNestCtx := ofString "blockNestCtx"

def bnParams : List MlS := [bnM, bnP]
def bnLocals : List MlS := [bnK, bnM0, bnCv, bnTy, bnQ, bnPq, bnL, bnU, bnY, bnX, bnR]

/-- `blockNestCtx` at the members' pointer block and `nP`: a record `[params block, lvls, holes block]`. -/
def bnBody (C : Ctx) : ProgHOL 64 := prologue bnLocals
  (.seq (.assign .local bnK (.load .one (vv bnM)))
  (.ite (.cmp .equal (vv bnK) (.const 0)) hang
  (.seq (.assign .local bnM0 (.load .one (.op .add [vv bnM, .const 8])))
  (.seq (.assign .local bnCv (.load .one (vv bnM0)))
  (.seq (.assign .local bnTy (.load .one (.op .add [vv bnCv, .const 16])))
  (.seq (.call (some (some (.local, bnQ), none)) fOpenFvars [vv bnP, vv bnTy, .const 0])
  (.ite (.cmp .equal (vv bnQ) (.const 0)) hang
  (.seq (.assign .local bnPq (.load .one (vv bnQ)))
  (.seq (.assign .local bnL (.load .one (.op .add [vv bnCv, .const 8])))
  (.seq (.call (some (some (.local, bnU), none)) fParamLevels [vv bnL])
  (allocP C bnY (.op .add [.panop .mul [vv bnK, .const 8], .const 8])
  (.seq (.store (vv bnY) (vv bnK))
  (.seq (.call (some (some (.local, bnX), none)) fNestHoles
      [vv bnM, vv bnPq, vv bnP, .op .add [vv bnY, .const 8], .const 0, vv bnK])
  (alloc3 C bnR (vv bnPq) (vv bnU) (vv bnY) (.return (vv bnR))))))))))))))))

/-- The code `blockNestCtx` runs. -/
structure BNCodes (C : Ctx) : Prop where
  self : C.code.lookup fBlockNestCtx = some (bnParams.map (fun p => (p, ShapeHOL.one)), bnBody C, .one)
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp1 : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ils : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  nh : C.code.lookup fNestHoles = some (nhParams.map (fun p => (p, ShapeHOL.one)), nhBody, .one)
  ip : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one)
  i1 : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  ic : Codes C (ExI.body C)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)

section
variable {σ : Type}

theorem bn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bnLocals → (ctxEnv C ++ bnParams.zip vals).get x = none :=
  Knot.params_none C bnLocals bnParams vals (by decide) (by decide)

/-- `blockNestCtx`'s answer: the context's fixed fields, and the record of its three computed parts. -/
def PostBN (C : Ctx) (p : BlockShape) (r : NestCtx × List EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ r.1.names = p.memberNames ∧ r.1.lps = p.lps ∧ r.1.nP = p.nP ∧
    r.1.nIdxs = p.nIdxs ∧ r.1.sort = p.resSort ∧ r.1.formers = p.formers ∧ ∃ or_ oq oh, w = cellA C or_ ∧
    H'[or_]? = some (cellA C oq) ∧ BlkAt H' oq (r.1.params.map Enc.idxW) ∧ H'[or_ + 1]? = some (Enc.idxW r.1.lvls) ∧
    H'[or_ + 2]? = some (cellA C oh) ∧ BlkAt H' oh (r.2.map Enc.idxW)

theorem postBN_locals (C : Ctx) (p : BlockShape) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBN C p a w s' st → PostBN C p a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

set_option maxHeartbeats 4000000 in
/-- **`blockNestCtx`**. -/
theorem bn_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BNCodes C)
    (p : BlockShape) (om : Nat) (H : List (BitVec 64)) (hp : C.H <+: H) (hM : PtrsRep C H om (MemberRep C H) p.members)
    (hb : p.nP + p.members.length < 2 ^ 56) (hml : p.members.length < 2 ^ 59) (hlp : p.lps.length < 2 ^ 59)
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (bnParams.zip [cellA C om, BitVec.ofNat 64 p.nP])) (bnBody C) s
      (blockNestCtx p) (PostBN (ctxH C H) p) := by
  refine specR_prologue (postBN_locals _ _) (bn_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  refine UD.specR_heapLoadI' (C := ctxH C H) bnK (vv bnM) om _ hM.1 (by decide)
    (by simp +decide [sev, Env.get, bnParams, ctxEnv]; rfl) ?_
  rcases hms : p.members with _ | ⟨m0, rest⟩
  · rw [hms] at hM
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hml' := hml
  rw [hms] at hml'; simp only [List.length_cons] at hml'
  have hK0 : BitVec.ofNat 64 (rest.length + 1) ≠ 0#64 := by
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hK0)
    (fun h => absurd rfl h) (fun _ => ?_)
  obtain ⟨om0, hm0, hrep0⟩ := hM.2 0 (by rw [hms]; simp)
  have hm0e : (p.members[0]'(by rw [hms]; simp)) = m0 := by simp [hms]
  rw [hm0e] at hrep0
  obtain ⟨⟨oc, hoc, hcv⟩, -⟩ := hrep0
  obtain ⟨-, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcv
  refine UD.specR_heapLoadI' (C := ctxH C H) bnM0 _ (om + 1 + 0) _ hm0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, bnParams, ctxEnv]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) bnCv (vv bnM0) om0 _ hoc (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) bnTy _ (oc + 2) _ hty (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
  unfold blockNestCtx
  simp only [BlockShape.formers, hms, List.map_cons]
  refine specR_callNIH (C := ctxH C H) bnQ fOpenFvars ofParams [vv bnP, vv bnTy, .const 0] (ofBody C)
    [BitVec.ofNat 64 p.nP, Enc.idxW m0.cvT.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ofc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, bnParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostOF (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
      w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
      (of_spec ra C hok hc.op p.nP m0.cvT.type 0 (by omega) (by omega) H hp s))
    (fun o1 w s1 H1 hp1 ⟨hn1, hs1⟩ => ?_)
  have hp1' : H <+: H1 := hp1
  rcases o1 with _ | ⟨pfv, pres⟩
  · rw [hn1 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨q1, oq, rfl, hq1a, -, hpfv⟩ := hs1 pfv pres rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
  have hq1l : q1 < H1.length := (List.getElem?_eq_some_iff.mp hq1a).1
  have hHN1' : H1.length ≤ C.HN := hHN1
  have hne1 : cellA C q1 ≠ 0 := cellA_ne0 C hok q1 (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) bnPq (vv bnQ) q1 _ hq1a (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) bnL _ (oc + 1) _ (get_prefix hwl hp1') (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc) ?_
  simp only [unwrapOr, pure_bind, BlockShape.nestCtx, bind_assoc]
  have hlps : p.lps = m0.cvT.levelParams := by simp [BlockShape.lps, hms]
  rw [hlps]
  have hwl' : wl = cellA C ol := hwlo
  subst hwl'
  refine specR_callNIH (C := ctxH C H1) bnU fParamLevels plParams [vv bnL] (plBody C) [cellA C ol] (by decide) rfl
    (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons], trivial⟩
    (PostLsH (ctxH C H1)) (fun h w _ _ => w = Enc.idxW h) (fun h w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
      (pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.ils m0.cvT.levelParams ol (by rw [← hlps]; exact hlp) H1 s1
        (eblk_mono hebl hp1')))
    (fun us wu s2 H2 hp2 hwu => ?_)
  subst hwu
  have hp2' : H1 <+: H2 := hp2
  have hpH2 : H <+: H2 := hp1'.trans hp2'
  rw [nestHoles]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN2 => ?_)
  have hHN2' : H2.length ≤ C.HN := hHN2
  refine specR_allocI (C := ctxH C H2) bnY _ (rest.length + 1 + 1) (by omega) (by decide)
    (fun v => by
      simp +decide [sev, Env.get_cons]; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H3 ws hp3 hws hroom3 => ?_)
  have hp3' : H2 <+: H3 := hp3
  have hroom3' : H3.length + (rest.length + 1 + 1) ≤ C.HN := hroom3
  have hl3 : (H3 ++ ws).length = H3.length + (rest.length + 1 + 1) := by simp [hws]
  refine specR_heapStoreI (ctxOK_H hok (H3 ++ ws)) (vv bnY) (vv bnK) H3.length
    (by show _ < (H3 ++ ws).length; omega) (BitVec.ofNat 64 (rest.length + 1))
    (by simp [sev, Env.get_cons]; rfl) (by simp +decide [sev, Env.get_cons]) ?_
  let H4 := (H3 ++ ws).set H3.length (BitVec.ofNat 64 (rest.length + 1))
  have hl4 : H4.length = H3.length + (rest.length + 1 + 1) := by simp [H4, hws]
  have h34 : H3 <+: H4 := prefix_set (List.prefix_append _ _) (by simp) _
  let H0 := H4.take (H3.length + 1)
  have h30 : H3 <+: H0 := prefix_take_of h34 (by omega)
  have h04 : H0 <+: H4 := List.take_prefix _ _
  have hhdr : H0[H3.length]? = some (BitVec.ofNat 64 (rest.length + 1)) := by
    simp only [H0, H4, List.getElem?_take]; rw [if_pos (by omega)]; exact List.getElem?_set_self (by simp [hws])
  have hM0 : PtrsRep C H om (MemberRep C H) (m0 :: rest) := by rw [← hms]; exact hM
  have hpH0 : H <+: H0 := (hpH2.trans hp3').trans h30
  have hpfv0 : BlkAt H0 oq (pfv.map Enc.idxW) := blkAt_mono hpfv ((hp2'.trans hp3').trans h30)
  refine specR_callNIG (C := ctxH (ctxH C (H3 ++ ws)) H4) bnX fNestHoles nhParams
    [vv bnM, vv bnPq, vv bnP, .op .add [vv bnY, .const 8], .const 0, vv bnK] nhBody
    [cellA C om, cellA C oq, BitVec.ofNat 64 p.nP, cellA C (H3.length + 1), BitVec.ofNat 64 0,
      BitVec.ofNat 64 (rest.length + 1)] (by decide) rfl (by decide) hc.nh
    ⟨by simp +decide [sev, Env.get_cons, Env.get, bnParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, bnParams, ctxEnv],
      by simp +decide [sev, Env.get_cons]; exact cellA_add8 C H3.length, rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostNH C H0 H4.length (H3.length + 1) 0 (rest.length + 1) []) (fun o _ _ H' => H0 <+: H' ∧
      ∃ ys, o = some ([] ++ ys) ∧ ys.length = rest.length + 1 - 0 ∧
        ∀ j (hj : j < ys.length), H'[H3.length + 1 + 0 + j]? = some (Enc.idxW ys[j]))
    (fun o w s' st ⟨H', hp', _, hs', h1⟩ => ⟨H', ⟨hp', h1⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nhParams _ rfl hlk) (by
      have := nh_spec (σ := σ) ra C hok hc.nh hc.ip hc.i1 hc.ic hc.fv
        { names := p.memberNames, lps := m0.cvT.levelParams, nP := p.nP,
          nIdxs := p.nIdxs, params := pfv, sort := p.resSort, formers := p.formers, lvls := us }
        (m0 :: rest) (by simp [BlockShape.formers, hms]) (by simp [BlockShape.memberNames, hms]) om oq (H3.length + 1) H0 (ptrsRep_mono hpH0 (fun _ _ h => memberRep_mono hpH0 h) hM0)
        hpfv0 (by simp; omega) (by simp; omega) (rest.length + 1) 0 H0 H4 s2 [] (by simp) (by simp) (List.prefix_refl _) h04
        (by simp only [H0, List.length_take, hl4]; omega) (by simp only [List.length_cons]; omega)
      simp only [List.drop_zero, List.length_cons] at this; exact this))
    (fun o w s3 H5 ⟨h05, ys, hys, hyl, hcells⟩ => ?_)
  subst hys
  simp only [List.nil_append, unwrapOr, pure_bind]
  have hpH5 : H <+: H5 := hpH0.trans h05
  refine specR_alloc3I (ctxOK_H hok H5) bnR (vv bnPq) (vv bnU) (vv bnY) (cellA C oq) (Enc.idxW us) (cellA C H3.length)
    (by decide) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons]; rfl)
    (fun H6 ws6 hp6 hws6 => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H6 ws6 (cellA C oq) (Enc.idxW us) (cellA C H3.length) hws6
  have hp56 : H5 <+: H6 := hp6
  have h6 := img3_prefix H6 ws6 (cellA C oq) (Enc.idxW us) (cellA C H3.length) hws6
  refine specR_returnI (vv bnR) (cellA C H6.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
  refine ⟨_, (hpH5.trans hp56).trans h6, sr_of_eq ht.sr rfl rfl rfl rfl, rfl, by simp [hlps], rfl, rfl, rfl, rfl,
    H6.length, oq, H3.length, rfl, g0, blkAt_mono hpfv0 ((h05.trans hp56).trans h6), g1, g2, ?_⟩
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [List.length_map, hyl, Nat.sub_zero]
    exact get_prefix (get_prefix hhdr h05) (hp56.trans h6)
  · simp only [List.length_map] at hj
    simp only [List.getElem_map]
    exact get_prefix (by simpa using hcells j hj) (hp56.trans h6)

end

end ConPanqueque.T.Ind
