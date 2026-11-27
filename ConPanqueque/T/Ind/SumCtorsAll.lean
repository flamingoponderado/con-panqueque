import ConPanqueque.T.Ind.SumCtor

/-!
# `checkBlockCtors` at any number of members

`scaBody(om, i, n, ol, nP, rs, ip, lg)`: member `i`'s constructors through `checkSumCtors` (`scs`, against the
member's own former and the block's level parameters at `ol`), then itself at `i + 1`. `sca_spec` refines
`checkBlockCtors mode fe fe p (p.members.drop i)`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def scaOm := ofString "sca_om"
def scaI := ofString "sca_i"
def scaN := ofString "sca_n"
def scaOl := ofString "sca_ol"
def scaNP := ofString "sca_np"
def scaRs := ofString "sca_rs"
def scaIp := ofString "sca_ip"
def scaLg := ofString "sca_lg"
def scaMi := ofString "sca_mi"
def scaOc := ofString "sca_oc"
def scaNi := ofString "sca_ni"
def scaOct := ofString "sca_oct"
def scaNct := ofString "sca_nct"
def scaX := ofString "sca_x"
def fSca := ofString "checkBlockCtorsAll"

def scaParams : List MlS := [scaOm, scaI, scaN, scaOl, scaNP, scaRs, scaIp, scaLg]
def scaLocals : List MlS := [scaMi, scaOc, scaNi, scaOct, scaNct, scaX]

def scaBody : ProgHOL 64 := prologue scaLocals
  (.ite (.cmp .lower (vv scaI) (vv scaN))
    (.seq (.assign .local scaMi (.load .one (.op .add [vv scaOm, .op .add [.panop .mul [vv scaI, .const 8], .const 8]])))
    (.seq (.assign .local scaOc (.load .one (vv scaMi)))
    (.seq (.assign .local scaNi (.load .one (.op .add [vv scaMi, .const 16])))
    (.seq (.assign .local scaOct (.load .one (.op .add [vv scaMi, .const 24])))
    (.seq (.assign .local scaNct (.load .one (vv scaOct)))
    (.seq (.call (some (some (.local, scaX), none)) fSumCtors
        [vv scaOct, .const 0, vv scaNct, vv scaOc, vv scaOl, vv scaNP, vv scaNi, vv scaRs, vv scaIp, vv scaLg])
    (.seq (.call (some (some (.local, scaX), none)) fSca
        [vv scaOm, .op .add [vv scaI, .const 1], vv scaN, vv scaOl, vv scaNP, vv scaRs, vv scaIp, vv scaLg])
      (.return (.const 0)))))))))
    (.return (.const 0)))

structure SCACodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  sc : SCCodes mode C
  scS : C.code.lookup fSumCtor = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody C, .one)
  scs : C.code.lookup fSumCtors = some (scsParams.map (fun p => (p, ShapeHOL.one)), scsBody, .one)
  self : C.code.lookup fSca = some (scaParams.map (fun p => (p, ShapeHOL.one)), scaBody, .one)

section
variable {σ : Type}

theorem sca_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ scaLocals → (ctxEnv C ++ scaParams.zip vals).get x = none :=
  Knot.params_none C scaLocals scaParams vals (by decide) (by decide)

/-- What one member's constructors need. -/
def SumMemberOK (C : Ctx) (nP : Nat) (ms : MemberShape) : Prop :=
  ms.nIdx < 2 ^ 56 ∧ ms.ctors.length < 2 ^ 58 ∧ ∀ i (hi : i < ms.ctors.length), SumCtorOK C nP ms.ctors[i]

set_option maxHeartbeats 16000000 in
/-- **`checkBlockCtors`** over the members from `i` on. -/
theorem sca_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : SCACodes mode C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (p : BlockShape) (om ol : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (hml : p.members.length < 2 ^ 58) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls p.resSort = some lsr)
    (hlp : p.lps.length < 2 ^ 59) (hbl : EBlk C.H ol (p.lps.map Enc.idxW))
    (hmo : ∀ ms ∈ p.members, SumMemberOK C p.nP ms) :
    ∀ f i (H : List (BitVec 64)) (s : AState), p.members.length - i = f → i ≤ p.members.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (scaParams.zip [cellA C om, BitVec.ofNat 64 i,
        BitVec.ofNat 64 p.members.length, cellA C ol, BitVec.ofNat 64 p.nP, Enc.idxW p.resSort, boolW p.isProp,
        boolW p.large])) scaBody s
        (checkBlockCtors mode C.fe C.fe p (p.members.drop i)) (Decl.PostU (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = p.members.length := by omega
    subst hin
    refine specR_prologue (Decl.postU_locals _) (sca_none _ _) ?_
    have hlw := nd_lt_iff p.members.length p.members.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, scaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < p.members.length := by omega
    refine specR_prologue (Decl.postU_locals _) (sca_none _ _) ?_
    have hlw := nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, scaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin]
    simp only [checkBlockCtors]
    obtain ⟨oi, hoi, hrep⟩ := hM.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -, hni, ⟨oct, hoct, hcsr⟩⟩ := hrep
    obtain ⟨hni56, hcl, hct⟩ := hmo _ (List.getElem_mem hin)
    refine UD.specR_heapLoadI' (C := ctxH C H) scaMi _ (om + 1 + i) _ (get_prefix hoi hp) (by decide)
      (by simp +decide [sev, Env.get, scaParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) scaOc (vv scaMi) oi _ (get_prefix hoc hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) scaNi _ (oi + 2) _ (get_prefix hni hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oi 2) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) scaOct _ (oi + 3) _ (get_prefix hoct hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oi 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) scaNct (vv scaOct) oct _ (get_prefix hcsr.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine specR_callNIH (C := ctxH C H) scaX fSumCtors scsParams
      [vv scaOct, .const 0, vv scaNct, vv scaOc, vv scaOl, vv scaNP, vv scaNi, vv scaRs, vv scaIp, vv scaLg] scsBody
      [cellA C oct, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members[i].ctors.length, cellA C oc, cellA C ol,
        BitVec.ofNat 64 p.nP, BitVec.ofNat 64 p.members[i].nIdx, Enc.idxW p.resSort, boolW p.isProp, boolW p.large]
      (by decide) rfl (by decide) hc.scs
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu scsParams _ rfl hlk)
        (by
          have h := scs_spec mode ra C hok hs hc.sc hc.scS hc.scs heqS p.lps p.nP p.members[i].nIdx p.resSort lsr hSd
            p.isProp p.large p.members[i].cvT p.members[i].ctors hni56 hlp hcl C.H (List.prefix_refl _) oct oc ol
            hcsr hcv hbl hct _ 0 H s rfl (Nat.zero_le _) hp
          rw [List.drop_zero] at h
          exact h))
      (fun r w s2 H2 hp2 _ => ?_)
    have hp2' : H <+: H2 := hp2
    refine specR_congr (m' := checkBlockCtors mode C.fe C.fe p (p.members.drop (i + 1)) >>= fun r => pure r)
      (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) scaX fSca scaParams
      [vv scaOm, .op .add [vv scaI, .const 1], vv scaN, vv scaOl, vv scaNP, vv scaRs, vv scaIp, vv scaLg] scaBody
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length, cellA C ol, BitVec.ofNat 64 p.nP,
        Enc.idxW p.resSort, boolW p.isProp, boolW p.large] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, scaParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu scaParams _ rfl hlk)
        (ih (i + 1) H2 s2 (by omega) (by omega) (hp.trans hp2')))
      (fun r w s3 H3 hp3 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp2'.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
