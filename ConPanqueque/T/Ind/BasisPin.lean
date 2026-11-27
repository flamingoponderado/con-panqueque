import ConPanqueque.T.Ind.PinLinks
import ConPanqueque.T.Decl.OffCheck

/-!
# A block under a pinned basis block's names, against its pin (`pinListOk`)

`bpnBody(o, k)`: the scratch tier off (else hang); the pinned block of kind word `k` (`1` `Eq`, `2` `Nat`, `3`
`Empty`, `4` `False`) interned literal by literal, its records kept (`genPinBlk`, the twin's `BasisKind.decls`,
a no-op at the fold's states); as many records as the pin's (else hang); then the twin's `pinListOk`:
`pinCopiesOk` (`pcsBody`) and `blockLinksOk` (`bllBody`, from the stream block's head's level parameters).
The port hangs unless both hold.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl ConPanqueque.T.Lit
open ConPanqueque.Start ConPanqueque.Logic.PlainIntern ConPanqueque.T.Quot

def bpO := ofString "bp_o"
def bpK := ofString "bp_k"
def bpQ := ofString "bp_q"
def bpN := ofString "bp_n"
def bpM := ofString "bp_m"
def bpX := ofString "bp_x"
def bpF := ofString "bp_f"
def fBpn := ofString "basisPinOk"

def bpnParams : List MlS := [bpO, bpK]
def bpnLocals : List MlS := [bpQ, bpN, bpM, bpX, bpF, ocA, ocB, ocC, ocD, qN, qL, qT, qU, qX, qW, vPn, vKa] ++
  pbLocs ++ genLocals

/-- A pinned basis block's kind word. -/
def basisWord : ConLeche.BasisKind → Nat
  | .eqK => 1
  | .natK => 2
  | .emptyK => 3
  | .falseK => 4
  | .quotK => 5

/-- After the pin's records: the counts, `pinCopiesOk`, `blockLinksOk`. -/
def bpnTail : ProgHOL 64 :=
  .seq (.assign .local bpN (.load .one (vv bpO)))
  (.seq (.assign .local bpM (.load .one (vv bpQ)))
  (.ite (.cmp .notEqual (vv bpN) (vv bpM)) hang
  (.seq (.call (some (some (.local, bpX), none)) fPcs [vv bpO, vv bpQ, .const 0, vv bpN])
  (.seq (.assign .local bpF (.load .one (.op .add [vv bpO, .const 8])))
  (.seq (.assign .local bpF (.load .one (.op .add [vv bpF, .const 16])))
  (.seq (.call (some (some (.local, bpX), none)) fBll [vv bpO, vv bpQ, .const 0, vv bpN, vv bpF])
    (.return (.const 1))))))))

/-- **A block under pinned block `k`'s names, against the pin** (hang unless `pinListOk` holds). -/
def bpnBody (C : Ctx) : ProgHOL 64 := prologue bpnLocals
  (offCheckP C
  (.ite (.cmp .equal (vv bpK) (.const 1)) (genPinBlk C bpQ (ConLeche.BasisKind.decls .eqK) bpnTail)
  (.ite (.cmp .equal (vv bpK) (.const 2)) (genPinBlk C bpQ (ConLeche.BasisKind.decls .natK) bpnTail)
  (.ite (.cmp .equal (vv bpK) (.const 3)) (genPinBlk C bpQ (ConLeche.BasisKind.decls .emptyK) bpnTail)
    (genPinBlk C bpQ (ConLeche.BasisKind.decls .falseK) bpnTail)))))

/-- The basis pin's code. -/
structure BPCodes (C : Ctx) : Prop where
  e : ECodes C
  pc : PCCodes C
  pl : PLCodes C
  self : C.code.lookup fBpn = some (bpnParams.map (fun p => (p, ShapeHOL.one)), bpnBody C, .one)

set_option maxRecDepth 100000 in
theorem basis_pinLits : ∀ k : ConLeche.BasisKind, k ≠ .quotK → ∀ c ∈ ConLeche.BasisKind.decls k, pinLitB c = true := by
  intro k hk c hc
  have : ∀ k ∈ [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK], ∀ c ∈ ConLeche.BasisKind.decls k,
      pinLitB c = true := by decide
  exact this k (by cases k <;> simp_all) c hc

theorem basis_len : ∀ k : ConLeche.BasisKind, k ≠ .quotK → 2 ≤ (ConLeche.BasisKind.decls k).length ∧
    (ConLeche.BasisKind.decls k).length ≤ 4 := by
  intro k hk; cases k <;> first | exact absurd rfl hk | decide

theorem basis_lps : ∀ k : ConLeche.BasisKind, k ≠ .quotK → ∀ c ∈ ConLeche.BasisKind.decls k,
    c.toConstantVal.levelParams.length ≤ 2 := by
  intro k hk c hc
  have := basis_pinLits k hk c hc
  simp only [pinLitB, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2

theorem denoteCIList_lps {st : EStore} : ∀ (cs : List IConstantInfo) (xs : List ConLeche.ConstantInfo),
    Frontend.denoteCIList st cs = some xs → ∀ c ∈ cs, ∃ x ∈ xs,
      c.toConstantVal.levelParams.length = x.toConstantVal.levelParams.length := by
  intro cs xs h c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨x, hx, hcx⟩ := denoteCIList_get cs xs i cs[i] h (List.getElem?_eq_getElem hi)
  exact ⟨x, List.mem_of_getElem? hx, denoteNList_length _ _
    (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hcx)).2.1⟩

section
variable {σ : Type}

theorem bpn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bpnLocals → (ctxEnv C ++ bpnParams.zip vals).get x = none :=
  Knot.params_none C bpnLocals bpnParams vals (by decide) (by decide)


set_option maxHeartbeats 8000000 in
/-- **After the pin's records**: the counts, then `pinListOk` (hang unless it holds). -/
theorem bpnTail_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BPCodes C)
    (blk pins : List IConstantInfo) (ob opb : Nat) (hbl : blk.length < 2 ^ 59) (hne : 0 < blk.length)
    (hlb : ∀ c ∈ blk, c.toConstantVal.levelParams.length < 2 ^ 59)
    (hlpn : ∀ c ∈ pins, c.toConstantVal.levelParams.length < 2 ^ 59)
    (B P : List ConLeche.ConstantInfo) (H0 H : List (BitVec 64)) (s : AState) (Γ : Env) (hp0 : H0 <+: H)
    (hpH : C.H <+: H) (hblk : IndBlk C H ob blk) (hpb : PinBlk C H opb pins)
    (hB : Frontend.denoteCIList s.store blk = some B) (hP : Frontend.denoteCIList s.store pins = some P)
    (hO : Γ.get bpO = some (cellA C ob)) (hQ : Γ.get bpQ = some (cellA C opb)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ bpnLocals)) bpnTail s (pinListOk blk pins)
      (PostPin (ctxH C H0) (fun b => b = true)) := by
  have hD : ∀ x ∈ bpnLocals, x ∈ ctxLocals ++ bpnLocals := fun x hx => List.mem_append_right _ hx
  unfold bpnTail
  obtain ⟨os, hosl, hosb, hosr⟩ := hblk
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hpb
  refine UD.specR_heapLoadI' (C := ctxH C H) bpN _ ob _ (by simpa [hosl, ctxH] using hosb.1)
    (hD _ (by simp [bpnLocals])) (by simp [sev, hO]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) bpM _ opb _ (by simpa [hpsl, ctxH] using hpsb.1)
    (hD _ (by simp [bpnLocals])) (by simp +decide [sev, Env.get_cons, hQ]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hpl61 : pins.length < 2 ^ 61 := by
    have := Ind.blkAt_len hok hHN hpsb; simp at this; omega
  refine specR_guardNe bpN bpM (BitVec.ofNat 64 blk.length) (BitVec.ofNat 64 pins.length)
    (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (fun hl => ?_)
  have hlen : blk.length = pins.length := natW_inj (by omega) (by omega) hl
  unfold pinListOk
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_callNIH (C := ctxH C H) bpX fPcs pcsParams [vv bpO, vv bpQ, .const 0, vv bpN] pcsBody
    [cellA C ob, cellA C opb, BitVec.ofNat 64 0, BitVec.ofNat 64 blk.length] (by decide) rfl
    (hD _ (by simp [bpnLocals])) hc.pc.pcs
    ⟨by simp +decide [sev, Env.get_cons, hO], by simp +decide [sev, Env.get_cons, hQ], rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (fun b w s' st => pinCopiesOk blk pins s = .ok (b, s') ∧ PostPin (ctxH C H) (fun b => b = true) b w s' st)
    (fun b _ s' _ => pinCopiesOk blk pins s = .ok (b, s') ∧ b = true)
    (fun a w s' st ⟨hr, h0, H', hp', hsr⟩ => ⟨H', hp', ⟨hr, h0⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (by
      have := pcs_spec (σ := σ) ra C hok hc.pc blk pins ob opb hlen hbl hlb B P _ 0 H s hpH ⟨os, hosl, hosb, hosr⟩
        ⟨ps, hpsl, hpsb, hpsr⟩ hB hP rfl (Nat.zero_le _)
      simp only [List.drop_zero] at this
      exact Knot.specR_of_pre u (pre_of_lookups hu pcsParams _ rfl hlk) this))
    (fun b w s1 H1 hp1 ⟨hr1, hb⟩ => ?_)
  subst hb
  simp only [if_true]
  obtain ⟨hst1, -⟩ := pinCopiesOk_run blk pins (sr_stateOK ht0.sr) ⟨ht0.sr.cok.rn, ht0.sr.cok.rl, ht0.sr.cok.rls⟩
    hB hP hr1
  have hp01 : H <+: H1 := hp1
  -- the head's level parameters
  have hb0 := hosb.2 0 (by simp; omega)
  simp only [List.getElem_map] at hb0
  have hci0 := hosr 0 hne (by omega)
  obtain ⟨ofm, hofm, hefm⟩ := cie_lps hci0
  refine UD.specR_heapLoadI' (C := ctxH C H1) bpF _ (ob + 1 + 0) _ (get_prefix hb0 hp01)
    (hD _ (by simp [bpnLocals])) (by simp +decide [sev, Env.get_cons, hO]; exact cellA_add8 C ob) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) bpF _ (os[0] + 2) _ (get_prefix hofm hp01)
    (hD _ (by simp [bpnLocals])) (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[0] 2) ?_
  unfold blockLinksOk
  have hfm : (blk.head?.map (·.toConstantVal.levelParams)).getD [] = blk[0].toConstantVal.levelParams := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hne]; rfl
  simp only [hfm]
  refine specR_congr (m' := blockLinksOkGo blk pins blk[0].toConstantVal.levelParams blk pins >>= fun b => pure b)
    (by simp) ?_
  refine specR_callNIH (C := ctxH C H1) bpX fBll bllParams [vv bpO, vv bpQ, .const 0, vv bpN, vv bpF] bllBody
    [cellA C ob, cellA C opb, BitVec.ofNat 64 0, BitVec.ofNat 64 blk.length, cellA C ofm] (by decide) rfl
    (hD _ (by simp [bpnLocals])) hc.pl.bll
    ⟨by simp +decide [sev, Env.get_cons, hO], by simp +decide [sev, Env.get_cons, hQ], rfl,
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (PostPinS (ctxH C H1) s1 (fun b => b = true)) (fun b _ _ _ => b = true)
    (fun a w s' st ⟨h0, _, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
    (fun u hu _ hlk => by
      have := bll_spec (σ := σ) C hok hc.pl blk pins ob opb ofm blk[0].toConstantVal.levelParams hlen hbl
        (hlb _ (List.getElem_mem hne)) hlb hlpn B P _ 0 H1 s1 (hpH.trans hp01)
        ⟨os, hosl, blkAt_mono hosb hp01, fun j hj ho => cie_mono hp01 (hosr j hj ho)⟩
        (pinBlk_mono ⟨ps, hpsl, hpsb, hpsr⟩ hp01) (eblk_mono hefm hp01) (denoteCIList_mono hst1.ext _ _ hB)
        (denoteCIList_mono hst1.ext _ _ hP) rfl (Nat.zero_le _)
      simp only [List.drop_zero] at this
      exact Knot.specR_of_pre u (pre_of_lookups hu bllParams _ rfl hlk) this)
    (fun b w s2 H2 hp2 hb2 => ?_)
  subst hb2
  exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H2, hp0.trans (hp01.trans hp2), sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem bpO_notQ : NotQ bpO :=
  notQ_of (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem bpQ_notQ : NotQ bpQ :=
  notQ_of (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxHeartbeats 16000000 in
/-- **A block under pinned block `kind`'s names, against the pin**: the port hangs unless `pinListOk` holds. -/
theorem bpn_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : BPCodes C)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (kind : ConLeche.BasisKind) (hk : kind ≠ .quotK) (blk : List IConstantInfo) (ob : Nat) (H : List (BitVec 64))
    (s : AState) (r : List IConstantInfo) (hpH : C.H <+: H) (hblk : IndBlk C H ob blk)
    (hdec : ConRon.Arena.BasisKind.decls kind s = .ok (r, s))
    (hlen : blk.length = (ConLeche.BasisKind.decls kind).length)
    (hlb : ∀ c ∈ blk, c.toConstantVal.levelParams.length < 2 ^ 59) (B : List ConLeche.ConstantInfo)
    (hB : Frontend.denoteCIList s.store blk = some B) :
    SpecR (σ := σ) (Pre (ctxH C H) s (bpnParams.zip [cellA C ob, BitVec.ofNat 64 (basisWord kind)])) (bpnBody C) s
      (pinListOk blk r) (PostPin (ctxH C H) (fun b => b = true)) := by
  refine specR_prologue (postPin_locals _ _) (bpn_none _ _) ?_
  have hD : ∀ x ∈ bpnLocals, x ∈ ctxLocals ++ bpnLocals := fun x hx => List.mem_append_right _ hx
  refine specR_fact (fun t ht => sr_stateOK ht.sr) (fun hst => ?_)
  refine specR_offCheckI ⟨hD _ (by simp [bpnLocals]), hD _ (by simp [bpnLocals]), hD _ (by simp [bpnLocals]),
    hD _ (by simp [bpnLocals])⟩ (fun hoff => ?_)
  obtain ⟨-, hden⟩ := ConRon.Bridge.BasisKind.decls_run hst hdec
  refine specR_okImp (m' := plainCIList (ConLeche.BasisKind.decls kind) >>= fun r' => pinListOk blk r')
    (fun a s' h => by
      obtain ⟨r', s1, h1, h2⟩ := AM.bind_ok h
      have e := basisDecls_plain kind hoff h1
      rw [hdec] at e
      cases e
      exact h2) ?_
  have G : GenEnv C (ctxLocals ++ bpnLocals) 12 :=
    ⟨hok, hf, hA, hc.e, hD _ (by simp [bpnLocals]), hD _ (by simp [bpnLocals]),
      fun c hc' j hj => hD _ (by
        have := gv_mem_genLocals hc' hj
        simp only [bpnLocals, List.mem_append]; exact Or.inr this)⟩
  have hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ ctxLocals ++ bpnLocals := fun x hx => hD x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bpnLocals])
  have hpb : ∀ l ∈ pbLocs, l ∈ ctxLocals ++ bpnLocals := fun l hl => hD l (by simp [bpnLocals, hl])
  have hne : 0 < blk.length := by have := (basis_len kind hk).1; omega
  have hbl : blk.length < 2 ^ 59 := by have := (basis_len kind hk).2; omega
  -- the common continuation
  have hrest : ∀ (Γ : Env), Γ.get bpO = some (cellA C ob) →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ bpnLocals))
        (genPinBlk C bpQ (ConLeche.BasisKind.decls kind) bpnTail) s
        (plainCIList (ConLeche.BasisKind.decls kind) >>= fun r' => pinListOk blk r')
        (PostPin (ctxH C H) (fun b => b = true)) := by
    intro Γ hO
    refine genPinBlk_spec ra G hq hpb bpQ (hD _ (by simp [bpnLocals])) bpQ_notQ (by decide) _ (basis_pinLits kind hk)
      (basis_len kind hk).2 H _ Γ [] s (fun r' s' Γ' H' o hp ag hr hres hpinb => ?_)
    have e := basisDecls_plain kind hoff hr
    rw [hdec] at e
    cases e
    have hlpn : ∀ c ∈ r, c.toConstantVal.levelParams.length < 2 ^ 59 := fun c hc' => by
      obtain ⟨x, hx, hl⟩ := denoteCIList_lps r _ hden c hc'
      have := basis_lps kind hk x hx; omega
    exact bpnTail_spec ra C hok hc blk r ob o hbl hne hlb hlpn B _ H H' s Γ' hp (hpH.trans hp)
      (indBlk_mono hblk hp) hpinb hB hden (by rw [ag bpO bpO_notQ (by decide)]; exact hO) hres
  have hO0 : ∀ (Γ : Env), (∀ y, y = bpO → Γ.get y = some (cellA C ob)) → Γ.get bpO = some (cellA C ob) :=
    fun Γ h => h bpO rfl
  cases kind with
  | eqK =>
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hrest _ (by simp +decide [Env.get_cons, Env.get, bpnParams, ctxEnv])
  | natK =>
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hrest _ (by simp +decide [Env.get_cons, Env.get, bpnParams, ctxEnv])
  | emptyK =>
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hrest _ (by simp +decide [Env.get_cons, Env.get, bpnParams, ctxEnv])
  | falseK =>
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, bpnParams, ctxEnv, basisWord,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hrest _ (by simp +decide [Env.get_cons, Env.get, bpnParams, ctxEnv])
  | quotK => exact absurd rfl hk

end

end ConPanqueque.T.Ind
