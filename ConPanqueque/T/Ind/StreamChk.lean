import ConPanqueque.T.Ind.StreamK

/-!
# The stream's recursor against the generated one (member class)

`srsBody`: the record's rules' shape against the class's constructors (names and field counts; the lengths are
checked by the caller). `srrBody`: each rule binds its arguments (`ruleBinds`) and its right-hand side is the
generated one (a different right-hand side hangs: the port compares handles only).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def srsW := ofString "srs_w"
def srsQ := ofString "srs_q"
def srsI := ofString "srs_i"
def srsN := ofString "srs_n"
def srsR := ofString "srs_r"
def srsC := ofString "srs_c"
def srsF := ofString "srs_f"
def srsO := ofString "srs_o"
def srsCn := ofString "srs_cn"
def srsCf := ofString "srs_cf"
def srsX := ofString "srs_x"
def fSrs := ofString "streamRulesShape"

def srsParams : List MlS := [srsW, srsQ, srsI, srsN]
def srsLocals : List MlS := [srsR, srsC, srsF, srsO, srsCn, srsCf, srsX]

def srsBody : ProgHOL 64 := prologue srsLocals
  (.ite (.cmp .lower (vv srsI) (vv srsN))
    (.seq (.assign .local srsR (.load .one (.op .add [vv srsW, .op .add [.panop .mul [vv srsI, .const 8], .const 8]])))
    (.seq (.assign .local srsC (.load .one (vv srsR)))
    (.seq (.assign .local srsF (.load .one (.op .add [vv srsR, .const 8])))
    (.seq (.assign .local srsO (.load .one (.op .add [vv srsQ, .op .add [.panop .mul [vv srsI, .const 16], .const 8]])))
    (.seq (.assign .local srsCn (.load .one (vv srsO)))
    (.seq (.assign .local srsCf (.load .one (.op .add [vv srsQ, .op .add [.panop .mul [vv srsI, .const 16], .const 16]])))
    (.ite (.cmp .equal (vv srsC) (vv srsCn))
      (.ite (.cmp .equal (vv srsF) (vv srsCf))
        (.seq (.call (some (some (.local, srsX), none)) fSrs [vv srsW, vv srsQ, .op .add [vv srsI, .const 1], vv srsN])
          (.return (.const 0)))
        hang)
      hang)))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem srs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ srsLocals → (ctxEnv C ++ srsParams.zip vals).get x = none :=
  Knot.params_none C srsLocals srsParams vals (by decide) (by decide)

/-- The state unchanged. -/
def PostSame (C : Ctx) (s : AState) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ SR C s' st

theorem postSame_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSame C s a w s' st → PostSame C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, h1⟩ => ⟨h0, sr_of_eq h1 rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`streamRulesShape`** from position `i` on, lengths equal. -/
theorem srs_spec (C : Ctx) (hc : C.code.lookup fSrs = some (srsParams.map (fun p => (p, ShapeHOL.one)), srsBody, .one))
    (rs : List IRecRule) (orl : Nat) (hl : C.H[orl]? = some (BitVec.ofNat 64 rs.length))
    (hr : ∀ i (hi : i < rs.length), ∃ q, C.H[orl + 1 + i]? = some (cellA C q) ∧ RuleE C.HB C.H q rs[i])
    (cs : List (IConstantVal × Nat)) (oq : Nat) (hcr : CtorsRep C C.H oq cs) (hlen : rs.length = cs.length)
    (hcl : cs.length < 2 ^ 58) :
    ∀ f i (s : AState), cs.length - i = f → i ≤ cs.length →
      SpecR (σ := σ) (Pre C s (srsParams.zip [cellA C orl, cellA C oq, BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length]))
        srsBody s (streamRulesShape (rs.drop i) (cs.drop i)) (PostSame C s) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = cs.length := by omega
    subst hin
    refine specR_prologue (postSame_locals C s) (srs_none _ _) ?_
    have hlw := nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, srsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, show rs.drop cs.length = [] by simp [hlen]]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < cs.length := by omega
    have hir : i < rs.length := by omega
    refine specR_prologue (postSame_locals C s) (srs_none _ _) ?_
    have hlw := nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, srsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨q, hq, hrq⟩ := hr i hir
    obtain ⟨hct, ⟨hnf, hnfb⟩, -, -⟩ := hrq
    refine UD.specR_heapLoadI' (C := C) srsR _ (orl + 1 + i) _ hq (by decide)
      (by simp +decide [sev, Env.get, srsParams, ctxEnv]; exact cellA_mulIdx C orl i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) srsC (vv srsR) q _ hct (by decide) (by simp [sev, Env.get_cons]) ?_
    refine UD.specR_heapLoadI' (C := C) srsF _ (q + 1) _ hnf (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q) ?_
    obtain ⟨oc, hoc, hcv, ⟨hcf, hcfb⟩⟩ := hcr.2 i hin
    refine UD.specR_heapLoadI' (C := C) srsO _ (oq + 1 + 2 * i) _ hoc (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, srsParams, ctxEnv]; exact cellA_pair1 C oq i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) srsCn (vv srsO) oc _ hcv.1 (by decide) (by simp [sev, Env.get_cons]) ?_
    refine UD.specR_heapLoadI' (C := C) srsCf _ (oq + 2 + 2 * i) _ hcf (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, srsParams, ctxEnv]; exact cellA_pair2 C oq i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hir, List.drop_eq_getElem_cons hin]
    simp only [streamRulesShape]
    by_cases hcn : rs[i].ctor = cs[i].1.name
    swap
    · have hne : Enc.idxW rs[i].ctor ≠ Enc.idxW cs[i].1.name := fun e => hcn (Enc.idxW_inj e)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hcn])
      (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases hnf' : rs[i].nfields = cs[i].2
    swap
    · have hne : BitVec.ofNat 64 rs[i].nfields ≠ BitVec.ofNat 64 cs[i].2 := fun e => hnf' (by
        have := congrArg BitVec.toNat e; simp at this; omega)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnf'])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [hcn, hnf', beq_self_eq_true, Bool.and_self, ite_true, pure_bind]
    refine specR_congr (m' := streamRulesShape (rs.drop (i + 1)) (cs.drop (i + 1)) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := C) srsX fSrs srsParams [vv srsW, vv srsQ, .op .add [vv srsI, .const 1], vv srsN] srsBody
      [cellA C orl, cellA C oq, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, srsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, srsParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, srsParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, srsParams, ctxEnv], trivial⟩
      (PostSame C s) (fun _ _ s' H' => H' = C.H ∧ s' = s) (fun a w s' st ⟨h0, h1⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, h0⟩, h1⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu srsParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s1 H1 hp1 ⟨eH, es⟩ => ?_)
    subst eH es
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The rules against the generated right-hand sides -/

def srrW := ofString "srr_w"
def srrG := ofString "srr_g"
def srrI := ofString "srr_i"
def srrN := ofString "srr_n"
def srrP := ofString "srr_p"
def srrR := ofString "srr_r"
def srrF := ofString "srr_f"
def srrH := ofString "srr_h"
def srrK := ofString "srr_k"
def srrY := ofString "srr_y"
def srrGv := ofString "srr_gv"
def srrX := ofString "srr_x"
def fSrr := ofString "streamRulesCheck"

def srrParams : List MlS := [srrW, srrG, srrI, srrN, srrP]
def srrLocals : List MlS := [srrR, srrF, srrH, srrK, srrY, srrGv, srrX]

def srrBody : ProgHOL 64 := prologue srrLocals
  (.ite (.cmp .lower (vv srrI) (vv srrN))
    (.seq (.assign .local srrR (.load .one (.op .add [vv srrW, .op .add [.panop .mul [vv srrI, .const 8], .const 8]])))
    (.seq (.assign .local srrF (.load .one (.op .add [vv srrR, .const 8])))
    (.seq (.assign .local srrH (.load .one (.op .add [vv srrR, .const 40])))
    (.seq (.assign .local srrK (.op .add [vv srrP, vv srrF]))
    (.seq (.call (some (some (.local, srrY), none)) fStripLams [vv srrK, vv srrH])
    (.ite (.cmp .equal (vv srrY) (.const 0)) hang
    (.seq (.assign .local srrGv (.load .one (.op .add [vv srrG, .op .add [.panop .mul [vv srrI, .const 8], .const 8]])))
    (.ite (.cmp .notEqual (vv srrH) (vv srrGv)) hang
    (.seq (.call (some (some (.local, srrX), none)) fSrr [vv srrW, vv srrG, .op .add [vv srrI, .const 1], vv srrN, vv srrP])
      (.return (.const 0)))))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem srr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ srrLocals → (ctxEnv C ++ srrParams.zip vals).get x = none :=
  Knot.params_none C srrLocals srrParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`streamRulesCheck`** from position `i` on (each rule's right-hand side the generated one). -/
theorem srr_spec (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fStripLams = some ([(pFu, .one), (pH, .one)], stripBody C fStripLams 5, .one))
    (hc : C.code.lookup fSrr = some (srrParams.map (fun p => (p, ShapeHOL.one)), srrBody, .one))
    (mode : ConLeche.CheckMode) (fe : IFEnv) (lps : List NIdx) (rP : Nat) (hrP : rP < 2 ^ 62)
    (rs : List IRecRule) (orl : Nat)
    (hr : ∀ i (hi : i < rs.length), ∃ q, C.H[orl + 1 + i]? = some (cellA C q) ∧ RuleE C.HB C.H q rs[i])
    (gs : List EIdx) (og : Nat) (hg : BlkAt C.H og (gs.map Enc.idxW)) (hlen : rs.length = gs.length)
    (hgl : gs.length < 2 ^ 58) :
    ∀ f i (H : List (BitVec 64)) (s : AState), gs.length - i = f → i ≤ gs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (srrParams.zip [cellA C orl, cellA C og, BitVec.ofNat 64 i, BitVec.ofNat 64 gs.length,
        BitVec.ofNat 64 rP])) srrBody s (streamRulesCheck mode fe lps rP (rs.drop i) (gs.drop i)) (Decl.PostU (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = gs.length := by omega
    subst hin
    refine specR_prologue (Decl.postU_locals _) (srr_none _ _) ?_
    have hlw := nd_lt_iff gs.length gs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, srrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, show rs.drop gs.length = [] by simp [hlen]]
    simp only [streamRulesCheck]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < gs.length := by omega
    have hir : i < rs.length := by omega
    refine specR_prologue (Decl.postU_locals _) (srr_none _ _) ?_
    have hlw := nd_lt_iff i gs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, srrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨q, hq, hrq⟩ := hr i hir
    obtain ⟨-, ⟨hnf, hnfb⟩, -, hrh⟩ := hrq
    refine UD.specR_heapLoadI' (C := ctxH C H) srrR _ (orl + 1 + i) _ (get_prefix hq hp) (by decide)
      (by simp +decide [sev, Env.get, srrParams, ctxEnv]; exact cellA_mulIdx C orl i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) srrF _ (q + 1) _ (get_prefix hnf hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) srrH _ (q + 5) _ (get_prefix hrh hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C q 5) ?_
    refine specR_assignI srrK _ (BitVec.ofNat 64 (rP + rs[i].nfields)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv]; rw [BitVec.ofNat_add]) ?_
    rw [List.drop_eq_getElem_cons hir, List.drop_eq_getElem_cons hin]
    simp only [streamRulesCheck, ruleBinds, bind_assoc]
    refine specR_callNIH (C := ctxH C H) srrY fStripLams [pFu, pH] [vv srrK, vv srrH] (stripBody C fStripLams 5)
      [BitVec.ofNat 64 (rP + rs[i].nfields), Enc.idxW rs[i].rhs] (by decide) rfl (by decide) hcs
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSP (ctxH C H)) (fun o w s' H' => (o = none → w = 0) ∧
        ∀ tys b, o = some (tys, b) → ∃ ob', w = cellA C ob' ∧ BlkAt H' ob' (tys.map Enc.idxW ++ [Enc.idxW b]))
      (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
      (fun u hu _ hlk => fun w hw => by
        subst hw; exact stripLams_spec C hok hcs (rP + rs[i].nfields) (by omega) H s rs[i].rhs _ (pre_of_lookups hu [pFu, pH] _ rfl hlk))
      (fun o w s1 H1 hp1 ⟨hn0, hsm⟩ => ?_)
    have hpH1 : H <+: H1 := hp1
    rcases o with _ | ⟨tys, bb⟩
    · have e0 := hn0 rfl
      subst e0
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨ob', rfl, hblk⟩ := hsm tys bb rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
    have hol := blkAt_lt hblk
    have hHN' : H1.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hne : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [pure_bind]
    have hgi := hg.2 i (by simp; omega)
    simp only [List.getElem_map] at hgi
    refine UD.specR_heapLoadI' (C := ctxH C H1) srrGv _ (og + 1 + i) _ (get_prefix hgi (hp.trans hpH1)) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv]; exact cellA_mulIdx C og i (by omega)) ?_
    by_cases heq : rs[i].rhs = gs[i]
    swap
    · have hne2 : Enc.idxW rs[i].rhs ≠ Enc.idxW gs[i] := fun e => heq (Enc.idxW_inj e)
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, heq])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [heq, beq_self_eq_true, Bool.not_true, ite_true, pure_bind]
    refine specR_congr (m' := streamRulesCheck mode fe lps rP (rs.drop (i + 1)) (gs.drop (i + 1)) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) srrX fSrr srrParams [vv srrW, vv srrG, .op .add [vv srrI, .const 1], vv srrN, vv srrP]
      srrBody [cellA C orl, cellA C og, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 gs.length, BitVec.ofNat 64 rP]
      (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, srrParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H1)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu srrParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hpH1)))
      (fun _ w s2 H2 hp2 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hpH1.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
