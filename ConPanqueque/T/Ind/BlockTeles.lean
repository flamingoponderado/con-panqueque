import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.SumCtor

/-!
# `checkBlockTeles` at any number of members

`ctlBody(om, i, n, nP)`: member `i`'s former through `checkBlockTele` (`ct`), then itself at `i + 1`; the sorts
come back as a linked list of cells `[sort, next]` ending in `0` (`SLink`). The constants `checkBlockTele` returns
are the members' own `cvT` (`PostCT`), so only the sorts are kept. `ctl_spec` refines
`checkBlockTeles mode fe nP (p.members.drop i)`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- A linked list of level handles: `0`, or a cell `[sort, next]`. -/
def SLink (B : BitVec 64) (H : List (BitVec 64)) : BitVec 64 → List LIdx → Prop
  | w, [] => w = 0
  | w, s :: ss => ∃ o w', w = B + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some (Enc.idxW s) ∧ H[o + 1]? = some w' ∧
      SLink B H w' ss

theorem sLink_mono {B : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ (ss : List LIdx) (w : BitVec 64), SLink B H w ss → SLink B H' w ss
  | [], _, h => h
  | _ :: ss, _, ⟨o, w', h1, h2, h3, h4⟩ => ⟨o, w', h1, get_prefix h2 hp, get_prefix h3 hp, sLink_mono hp ss w' h4⟩

theorem sameLay_St (C : Ctx) (St : EStore) : SameLay C (ctxSt C St) := rfl

def ctlOm := ofString "ctl_om"
def ctlI := ofString "ctl_i"
def ctlN := ofString "ctl_n"
def ctlNP := ofString "ctl_np"
def ctlMi := ofString "ctl_mi"
def ctlOc := ofString "ctl_oc"
def ctlNi := ofString "ctl_ni"
def ctlK := ofString "ctl_k"
def ctlT := ofString "ctl_t"
def ctlR := ofString "ctl_r"
def ctlX := ofString "ctl_x"
def fCtl := ofString "checkBlockTelesAll"

def ctlParams : List MlS := [ctlOm, ctlI, ctlN, ctlNP]
def ctlLocals : List MlS := [ctlMi, ctlOc, ctlNi, ctlK, ctlT, ctlR, ctlX]

def ctlBody (C : Ctx) : ProgHOL 64 := prologue ctlLocals
  (.ite (.cmp .lower (vv ctlI) (vv ctlN))
    (.seq (.assign .local ctlMi (.load .one (.op .add [vv ctlOm, .op .add [.panop .mul [vv ctlI, .const 8], .const 8]])))
    (.seq (.assign .local ctlOc (.load .one (vv ctlMi)))
    (.seq (.assign .local ctlNi (.load .one (.op .add [vv ctlMi, .const 16])))
    (.seq (.assign .local ctlK (.op .add [vv ctlNP, vv ctlNi]))
    (.seq (.call (some (some (.local, ctlT), none)) fBlockTele [vv ctlOc, vv ctlK])
    (.seq (.call (some (some (.local, ctlR), none)) fCtl [vv ctlOm, .op .add [vv ctlI, .const 1], vv ctlN, vv ctlNP])
    (alloc2 C ctlX (vv ctlT) (vv ctlR) (.return (vv ctlX)))))))))
    (.return (.const 0)))

structure CTLCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ccv : CcvCodes mode C
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ct : C.code.lookup fBlockTele = some (ctParams.map (fun p => (p, ShapeHOL.one)), ctBody, .one)
  self : C.code.lookup fCtl = some (ctlParams.map (fun p => (p, ShapeHOL.one)), ctlBody C, .one)

section
variable {σ : Type}

theorem ctl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ctlLocals → (ctxEnv C ++ ctlParams.zip vals).get x = none :=
  Knot.params_none C ctlLocals ctlParams vals (by decide) (by decide)

/-- After the tele loop: the constants are the members' formers, the sorts a linked list, each denoted. -/
def PostCTL (C : Ctx) (ms : List MemberShape) (r : List (IConstantVal × LIdx)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ r.map Prod.fst = ms.map (·.cvT) ∧ SLink C.HB H' w (r.map Prod.snd) ∧
    ∀ x ∈ r, ∃ l, denoteL s'.store.ls x.2 = some l

theorem postCTL_locals (C : Ctx) (ms : List MemberShape) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostCTL C ms a w s' st → PostCTL C ms a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2, h3⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2, h3⟩

theorem postCTL_lower {C : Ctx} {St : EStore} (hx : Ext C.St St) (ms : List MemberShape) :
    ∀ a w s' (st : PState σ), PostCTL (ctxSt C St) ms a w s' st → PostCTL C ms a w s' st :=
  fun _ _ _ _ ⟨H', hp, hs, h1, h2, h3⟩ => ⟨H', hp, sr_lower (C := ctxH C H') hs hx, h1, h2, h3⟩

/-- The member facts the tele loop reads. -/
def TeleOK (C : Ctx) (ms : MemberShape) : Prop :=
  ms.nIdx < 2 ^ 62 ∧ ms.cvT.levelParams.length < 2 ^ 62 ∧
    ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = ms.cvT.levelParams.length,
      ∀ j (hj : j < ms.cvT.levelParams.length), denoteN C.St.ns ms.cvT.levelParams[j] = some (ks[j]'(by omega))

theorem teleOK_ext {C : Ctx} {St : EStore} (hx : Ext C.St St) {ms : MemberShape} (h : TeleOK C ms) :
    TeleOK (ctxSt C St) ms :=
  let ⟨h1, h2, ks, hkl, hks⟩ := h
  ⟨h1, h2, ks, hkl, fun j hj => denoteN_ext (hks j hj) hx⟩

set_option maxHeartbeats 16000000 in
/-- **`checkBlockTeles`** over the members from `i` on (any context of the same layout). -/
theorem ctl_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (p : BlockShape) (om : Nat)
    (hml : p.members.length < 2 ^ 58) (hnP : p.nP < 2 ^ 62) :
    ∀ f (C : Ctx), CtxOK C → C.side = false → CTLCodes mode C → PtrsRep C C.H om (MemberRep C C.H) p.members →
      (∀ ms ∈ p.members, TeleOK C ms) →
      ∀ i (H : List (BitVec 64)) (s : AState), p.members.length - i = f → i ≤ p.members.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (ctlParams.zip [cellA C om, BitVec.ofNat 64 i,
        BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP])) (ctlBody C) s
        (checkBlockTeles mode C.fe p.nP (p.members.drop i)) (PostCTL (ctxH C H) (p.members.drop i)) := by
  intro f
  induction f with
  | zero =>
    intro C hok hs hc hM hT i H s hf hi hp
    have hin : i = p.members.length := by omega
    subst hin
    refine specR_prologue (postCTL_locals _ _) (ctl_none _ _) ?_
    have hlw := nd_lt_iff p.members.length p.members.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ctlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl, rfl, rfl,
      fun x hx => absurd hx (by simp)⟩)
  | succ f ih =>
    intro C hok hs hc hM hT i H s hf hi hp
    have hin : i < p.members.length := by omega
    refine specR_prologue (postCTL_locals _ _) (ctl_none _ _) ?_
    have hlw := nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ctlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin]
    simp only [checkBlockTeles]
    obtain ⟨oi, hoi, hrep⟩ := hM.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -, hni, -⟩ := hrep
    obtain ⟨hmn, hmk, ks, hkl, hks⟩ := hT _ (List.getElem_mem hin)
    refine UD.specR_heapLoadI' (C := ctxH C H) ctlMi _ (om + 1 + i) _ (get_prefix hoi hp) (by decide)
      (by simp +decide [sev, Env.get, ctlParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ctlOc (vv ctlMi) oi _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ctlNi _ (oi + 2) _ (get_prefix hni hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oi 2) ?_
    refine specR_assignI ctlK _ (BitVec.ofNat 64 (p.nP + p.members[i].nIdx)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, ctlParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat]) ?_
    refine specR_callNIH (C := ctxH C H) ctlT fBlockTele ctParams [vv ctlOc, vv ctlK] ctBody
      [cellA C oc, BitVec.ofNat 64 (p.nP + p.members[i].nIdx)] (by decide) rfl (by decide) hc.ct
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostCT (ctxH C H) p.members[i].cvT)
      (fun r w s' H' => r.1 = p.members[i].cvT ∧ w = Enc.idxW r.2 ∧ ∃ l, denoteL s'.store.ls r.2 = some l)
      (fun r w s' st ⟨h1, h2, ⟨H', hp', hsr⟩, h3⟩ => ⟨H', hp', ⟨h1, h2, h3⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctParams _ rfl hlk)
        (ct_spec mode C.fe ra C hok hs hc.ccv hc.sp hc.srt rfl p.nP p.members[i] oc (by omega) H hp (cvRep_mono hp hcv)
          hmk ks hkl hks s))
      (fun r w s1 H1 hp1 ⟨hr1, hw1, l0, hl0⟩ => ?_)
    obtain ⟨cv, sr⟩ := r
    simp only at hr1 hw1 hl0
    subst hr1 hw1
    have hp1' : H <+: H1 := hp1
    refine specR_atEntry fun t1 ht1 => ?_
    have hx1 : Ext C.St s1.store := ht1.sr.floor
    refine specR_invRaise (R' := PostCTL (ctxSt (ctxH C H) s1.store) (p.members[i] :: p.members.drop (i + 1))) ?_
      (fun a w s' t _ hpost => postCTL_lower (C := ctxH C H) hx1 _ a w s' t hpost)
    set C1 := ctxSt C s1.store with hC1
    have hok1 : CtxOK C1 := ctxOK_St hok _
    have hc1 : CTLCodes mode C1 := by ctx_tr hc
    show SpecR (Inv (ctxH C1 H1) s1 _ _ _) _ _ _ _
    refine specR_callNIH (C := ctxH C1 H1) ctlR fCtl ctlParams
      [vv ctlOm, .op .add [vv ctlI, .const 1], vv ctlN, vv ctlNP] (ctlBody C1)
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP]
      (by decide) rfl (by decide) hc1.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ctlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ctlParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, ctlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ctlParams, ctxEnv], trivial⟩
      (PostCTL (ctxH C1 H1) (p.members.drop (i + 1)))
      (fun rs w s' H' => rs.map Prod.fst = (p.members.drop (i + 1)).map (·.cvT) ∧ SLink C.HB H' w (rs.map Prod.snd) ∧
        ∀ x ∈ rs, ∃ l, denoteL s'.store.ls x.2 = some l)
      (fun rs w s' st ⟨H', hp', hsr, h1, h2, h3⟩ => ⟨H', hp', ⟨h1, h2, h3⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctlParams _ rfl hlk)
        (ih C1 hok1 hs hc1 hM (fun ms hm => teleOK_ext hx1 (hT ms hm)) (i + 1) H1 s1 (by omega) (by omega)
          (hp.trans hp1')))
      (fun rs w s2 H2 hp2 ⟨h1, h2, h3⟩ => ?_)
    have hp2' : H1 <+: H2 := hp2
    refine specR_alloc2I (ctxOK_H hok1 H2) ctlX (vv ctlT) (vv ctlR) (Enc.idxW sr) w (by decide)
      (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun H3 ws hp3 hws => ?_)
    obtain ⟨k0, k1⟩ := img2_get H3 ws (Enc.idxW sr) w hws
    have hp3' : H2 <+: _ := (hp3 : H2 <+: H3).trans (img2_prefix H3 ws (Enc.idxW sr) w hws)
    refine specR_returnI (vv ctlX) (cellA C H3.length) (by simp +decide [sev, Env.get_cons]; rfl) (fun t ht => ?_)
    refine ⟨_, hp1'.trans (hp2'.trans hp3'), sr_of_eq ht.sr rfl rfl rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.map_cons, h1]
    · exact ⟨H3.length, w, rfl, k0, k1, sLink_mono hp3' _ _ h2⟩
    · intro x hx
      rcases List.mem_cons.mp hx with e | hx'
      · subst e; exact ⟨l0, denoteL_ext hl0 ht.sr.floor⟩
      · obtain ⟨l, hl⟩ := h3 x hx'
        exact ⟨l, hl⟩

end

end ConPanqueque.T.Ind
