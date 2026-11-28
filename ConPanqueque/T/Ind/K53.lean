import ConPanqueque.T.Ind.GenPre
import ConPanqueque.T.Ind.EraseFVars
import ConPanqueque.T.Ind.PiCount
import ConPanqueque.T.Ind.KindDecode

/-!
# Node agreement at a recursive field (`targetK53`, `classNodesAgree`, `classFieldsAgree`)

`elm`: `mapM eraseFVarTys` over a block's prefix.  `tkb`: a block's slice.  `k53`: `targetK53` (every `false` of
the twin hangs).  `cnd`: `classNodesAgree` over a class's table entries of one constructor.  `cfg`:
`classFieldsAgree` over the kinds block (`0` ordinary, `tele + 1` recursive at class `0`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- The elements of a block at `pa` from position `0` are `xs` (the block may hold more). -/
def ElemsAt (H : List (BitVec 64)) (pa : Nat) (xs : List EIdx) : Prop :=
  ∀ j (hj : j < xs.length), H[pa + 1 + j]? = some (Enc.idxW xs[j])

theorem elemsAt_mono {H H' : List (BitVec 64)} (hp : H <+: H') {pa : Nat} {xs : List EIdx} (h : ElemsAt H pa xs) :
    ElemsAt H' pa xs := fun j hj => get_prefix (h j hj) hp

theorem elemsAt_of_blk {H : List (BitVec 64)} {pa : Nat} {xs : List EIdx} {ys : List (BitVec 64)}
    (h : BlkAt H pa (xs.map Enc.idxW ++ ys)) : ElemsAt H pa xs := fun j hj => by
  have := h.2 j (by simp; omega)
  rwa [List.getElem_append_left (by simpa using hj), List.getElem_map] at this

theorem elemsAt_bound {H : List (BitVec 64)} {pa : Nat} {xs : List EIdx} (h : ElemsAt H pa xs) (j : Nat)
    (hj : j < xs.length) : pa + 1 + j < H.length := (List.getElem?_eq_some_iff.mp (h j hj)).1

/-! ## `mapM eraseFVarTys` over a block -/

def elmA := ofString "elm_a"
def elmI := ofString "elm_i"
def elmN := ofString "elm_n"
def elmX := ofString "elm_x"
def fElm := ofString "eraseList"

def elmParams : List MlS := [elmA, elmI, elmN]
def elmLocals : List MlS := gaaLocals ++ [elmX]

def elmBody (C : Ctx) : ProgHOL 64 := prologue elmLocals
  (.ite (.cmp .lower (vv elmI) (vv elmN))
    (.seq (.assign .local elmX (.load .one (.op .add [vv elmA, .op .add [.panop .mul [vv elmI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, elmX), none)) fEft [vv elmX])
    (.seq (.call (some (some (.local, ExS.lY), none)) fElm [vv elmA, .op .add [vv elmI, .const 1], vv elmN])
      (prependP C elmX))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

structure ELMCodes (C : Ctx) : Prop where
  eft : EFTCodes C
  self : C.code.lookup fElm = some (elmParams.map (fun p => (p, ShapeHOL.one)), elmBody C, .one)

section
variable {σ : Type}

theorem elm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ elmLocals → (ctxEnv C ++ elmParams.zip vals).get x = none :=
  Knot.params_none C elmLocals elmParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`(xs.drop i).mapM eraseFVarTys`**, a fresh block. -/
theorem elm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : ELMCodes C)
    (xs : List EIdx) (pa : Nat) (hxl : xs.length < 2 ^ 61) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0)
    (hA : ElemsAt H0 pa xs) :
    ∀ f i (H : List (BitVec 64)) (s : AState), xs.length - i = f → i ≤ xs.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (elmParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 xs.length]))
        (elmBody C) s ((xs.drop i).mapM eraseFVarTys) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = xs.length := by omega
    subst hin
    refine specR_prologue (postA_locals _) (elm_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, elmParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [List.mapM_nil]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < xs.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (postA_locals _) (elm_none _ _) ?_
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, elmParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hx := hA i hin
    refine UD.specR_heapLoadI' (C := ctxH C H) elmX _ (pa + 1 + i) _ (get_prefix hx hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, elmParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin, List.mapM_cons]
    refine specR_callNIH (C := ctxH C H) elmX fEft eftParams [vv elmX] eftBody [Enc.idxW xs[i]] (by decide) rfl
      (by decide) hc.eft.self ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (PostK (ctxH C H)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu eftParams _ rfl hlk)
        (eft_spec ra C hok hc.eft H hpC s xs[i]))
      (fun e w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fElm elmParams [vv elmA, .op .add [vv elmI, .const 1], vv elmN]
      (elmBody C) [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, elmParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, elmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, elmParams, ctxEnv], trivial⟩
      (PostA (ctxH C H1)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
      (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu elmParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun rs w s2 H2 hp2 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    refine specR_congr (m' := pure (e :: rs)) (by simp) ?_
    refine ExPre.prepend_spec C hok (H := H2) elmX (Enc.idxW e) oy (rs.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, elmParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, hp1'.trans (hp2'.trans hp'), rfl, by simpa using hb, hsr⟩

end

/-! ## A block's slice -/

def tkbA := ofString "tkb_a"
def tkbI := ofString "tkb_i"
def tkbN := ofString "tkb_n"
def tkbX := ofString "tkb_x"
def fTkb := ofString "blockSlice"

def tkbParams : List MlS := [tkbA, tkbI, tkbN]
def tkbLocals : List MlS := gaaLocals ++ [tkbX]

def tkbBody (C : Ctx) : ProgHOL 64 := prologue tkbLocals
  (.ite (.cmp .lower (vv tkbI) (vv tkbN))
    (.seq (.assign .local tkbX (.load .one (.op .add [vv tkbA, .op .add [.panop .mul [vv tkbI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, ExS.lY), none)) fTkb [vv tkbA, .op .add [vv tkbI, .const 1], vv tkbN])
      (prependP C tkbX)))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem tkb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tkbLocals → (ctxEnv C ++ tkbParams.zip vals).get x = none :=
  Knot.params_none C tkbLocals tkbParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`(xs.take n).drop i`**, a fresh block (the state kept). -/
theorem tkb_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fTkb = some (tkbParams.map (fun p => (p, ShapeHOL.one)), tkbBody C, .one))
    (xs : List EIdx) (pa n : Nat) (hn : n ≤ xs.length) (hxl : xs.length < 2 ^ 61) (H0 : List (BitVec 64))
    (hp0 : C.H <+: H0) (hA : ElemsAt H0 pa xs) :
    ∀ f i (H : List (BitVec 64)) (s : AState), n - i = f → i ≤ n → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (tkbParams.zip [cellA C pa, BitVec.ofNat 64 i, BitVec.ofNat 64 n]))
        (tkbBody C) s (pure ((xs.take n).drop i)) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = n := by omega
    subst hin
    refine specR_prologue (postA_locals _) (tkb_none _ _) ?_
    have hlw := nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tkbParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (show ((xs.take i).length ≤ i) by simp)]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      (hp2 : H <+: H2).trans hpr', rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < n := by omega
    refine specR_prologue (postA_locals _) (tkb_none _ _) ?_
    have hlw := nd_lt_iff i n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tkbParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hx := hA i (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) tkbX _ (pa + 1 + i) _ (get_prefix hx hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tkbParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    have hdc : (xs.take n).drop i = xs[i] :: (xs.take n).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    rw [hdc]
    refine specR_congr (m' := (pure ((xs.take n).drop (i + 1)) : AM (List EIdx)) >>= fun r => pure (xs[i] :: r))
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fTkb tkbParams [vv tkbA, .op .add [vv tkbI, .const 1], vv tkbN]
      (tkbBody C) [cellA C pa, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 n] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, tkbParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tkbParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, tkbParams, ctxEnv], trivial⟩
      (PostA (ctxH C H)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
      (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tkbParams _ rfl hlk)
        (ih (i + 1) H s (by omega) (by omega) hp))
      (fun rs w s2 H2 hp2 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp2' : H <+: H2 := hp2
    refine ExPre.prepend_spec C hok (H := H2) tkbX (Enc.idxW xs[i]) oy (rs.map Enc.idxW) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hry (by decide)
      (by simp +decide [Env.get_cons, Env.get, tkbParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, hp2'.trans hp', rfl, by simpa using hb, hsr⟩

end

/-! ## `targetK53` -/

def k53Tb := ofString "k53_tb"
def k53Tn := ofString "k53_tn"
def k53Mj := ofString "k53_mj"
def k53F := ofString "k53_f"
def k53Npc := ofString "k53_npc"
def k53Ms := ofString "k53_ms"
def k53Us := ofString "k53_us"
def k53Olp := ofString "k53_olp"
def k53Ty0 := ofString "k53_ty0"
def k53Pp := ofString "k53_pp"
def k53Pn := ofString "k53_pn"
def k53Pa := ofString "k53_pa"
def k53Nd := ofString "k53_nd"
def k53Nm := ofString "k53_nm"
def k53Sp := ofString "k53_sp"
def k53Wl := ofString "k53_wl"
def k53Lw := ofString "k53_lw"
def k53Ew := ofString "k53_ew"
def k53Et := ofString "k53_et"
def k53Q := ofString "k53_q"
def k53Lh := ofString "k53_lh"
def k53Mh := ofString "k53_mh"
def k53I1 := ofString "k53_i1"
def k53U1 := ofString "k53_u1"
def k53I2 := ofString "k53_i2"
def k53La := ofString "k53_la"
def k53Ma := ofString "k53_ma"
def k53Ll := ofString "k53_ll"
def k53Ml := ofString "k53_ml"
def k53Le := ofString "k53_le"
def k53Me := ofString "k53_me"
def k53Lp := ofString "k53_lp"
def k53Hd := ofString "k53_hd"
def k53Ap := ofString "k53_ap"
def k53O := ofString "k53_o"
def k53R := ofString "k53_r"
def fK53 := ofString "targetK53"

def k53Params : List MlS := [k53Tb, k53Tn, k53Mj, k53F, k53Npc, k53Ms, k53Us, k53Olp, k53Ty0, k53Pp, k53Pn, k53Pa,
  k53Nd, k53Nm]
def k53Locals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, k53Sp, k53Wl, k53Lw, k53Ew, k53Et, k53Q, k53Lh, k53Mh,
  k53I1, k53U1, k53I2, k53La, k53Ma, k53Ll, k53Ml, k53Le, k53Me, k53Lp, k53Hd, k53Ap, k53O, k53R]

/-- The tail after both heads are constants. -/
def k53Tail : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv k53Lh)) (.seq eViewP
  (.seq (.assign .local k53I1 (.load .one (vv lRp)))
  (.seq (.assign .local k53U1 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv k53Mh)) (.seq eViewP
  (.seq (.assign .local k53I2 (.load .one (vv lRp)))
  (.seq (.call (some (some (.local, k53La), none)) fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Lw])
  (.seq (.call (some (some (.local, k53Ma), none)) fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Mj])
  (.seq (.assign .local k53Ll (.load .one (vv k53La)))
  (.seq (.assign .local k53Ml (.load .one (vv k53Ma)))
  (.ite (.cmp .equal (vv k53I1) (vv k53I2))
  (.ite (.cmp .equal (vv k53Ll) (vv k53Ml))
  (.ite (.cmp .lower (vv k53Ll) (vv k53Npc)) hang
  (.seq (.call (some (some (.local, k53Le), none)) fElm [vv k53La, vv k53Npc, vv k53Ll])
  (.seq (.call (some (some (.local, k53Me), none)) fElm [vv k53Ma, vv k53Npc, vv k53Ml])
  (.seq (.call (some (some (.local, k53Q), none)) fBlkEq [vv k53Le, vv k53Me, .const 0])
  (.ite (.cmp .equal (vv k53Q) (.const 0)) hang
  (.seq (.call (some (some (.local, k53Lp), none)) fTkb [vv k53La, .const 0, vv k53Npc])
  (.seq (.call (some (some (.local, k53Hd), none)) fInternConst [vv k53I1, vv k53U1])
  (.seq (.call (some (some (.local, k53Ap), none)) ExK.fMka [vv k53Hd, vv k53Lp, .const 0, vv k53Npc])
  (.seq (.call (some (some (.local, k53O), none)) fNocTop [vv k53Ap, vv k53Ms, .const 0, .const 0])
  (.ite (.cmp .equal (vv k53O) (.const 0)) hang
  (.seq (.call (some (some (.local, k53R), none)) fTcc [vv k53Us, vv k53U1, vv k53Olp, vv k53Ms, vv k53Pp, vv k53Pn,
      vv k53Pa, vv k53Lp, vv k53Nd])
    (.return (vv k53R)))))))))))))
  hang) hang)))))))))))))

def k53Body : ProgHOL 64 := prologue k53Locals
  (.seq (.call (some (some (.local, k53Sp), none)) fStripPis [vv k53Tn, vv k53F])
  (.ite (.cmp .equal (vv k53Sp) (.const 0)) hang
  (.seq (.assign .local k53Wl (.load .one (vv k53Sp)))
  (.seq (.assign .local k53Wl (.op .sub [vv k53Wl, .const 1]))
  (.seq (.assign .local k53Lw (.load .one (.op .add [vv k53Sp, .op .add [.panop .mul [vv k53Wl, .const 8], .const 8]])))
  (.seq (.call (some (some (.local, k53Ew), none)) fElm [vv k53Sp, .const 0, vv k53Wl])
  (.seq (.call (some (some (.local, k53Et), none)) fElm [vv k53Tb, .const 0, vv k53Tn])
  (.seq (.call (some (some (.local, k53Q), none)) fBlkEq [vv k53Ew, vv k53Et, .const 0])
  (.ite (.cmp .equal (vv k53Q) (.const 0)) hang
  (.seq (.call (some (some (.local, k53Lh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Lw])
  (.seq (.call (some (some (.local, k53Mh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Mj])
  (.ite (tagIsE k53Lh 3) (.ite (tagIsE k53Mh 3) k53Tail hang) hang))))))))))))

structure K53Codes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  elm : ELMCodes C
  be : C.code.lookup fBlkEq = some (beParams.map (fun p => (p, ShapeHOL.one)), beBody, .one)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  tkb : C.code.lookup fTkb = some (tkbParams.map (fun p => (p, ShapeHOL.one)), tkbBody C, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  nt : NTCodes C
  tcc : TCCCodes mode C
  self : C.code.lookup fK53 = some (k53Params.map (fun p => (p, ShapeHOL.one)), k53Body, .one)

section
variable {σ : Type}

theorem k53_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ k53Locals → (ctxEnv C ++ k53Params.zip vals).get x = none :=
  Knot.params_none C k53Locals k53Params vals (by decide) (by decide)

/-- A block in the heap is shorter than `2 ^ 61`. -/
theorem blk_len_lt {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} (hHN : H.length ≤ C.HN) {o : Nat}
    {xs : List (BitVec 64)} (h : BlkAt H o xs) : xs.length < 2 ^ 61 := by
  have hlay := hok.heapLay
  have := (List.getElem?_eq_some_iff.mp h.1).1
  rcases Nat.eq_zero_or_pos xs.length with h0 | hpos
  · omega
  · have h1 := h.2 (xs.length - 1) (by omega)
    have := (List.getElem?_eq_some_iff.mp h1).1
    omega

set_option maxHeartbeats 64000000 in
/-- **`targetK53`** at one recorded field `f`, the call's telescope and leaf a block `tele ++ [leaf]` (every `false`
hangs). -/
theorem k53_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : K53Codes mode C) (p : BlockShape) (fts : List EIdx) (hfts : fts = p.formers.map (·.type)) (hml : p.members.length < 2 ^ 58)
    (wty wnm : BitVec 64)
    (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (Mc : TargetMajor) (olp pp pa : Nat) (hlpl : p.lps.length < 2 ^ 59) (hdl : Mc.ds.length < 2 ^ 58)
    (hpl : Mc.pfvs.length < 2 ^ 58) (hnpc : Mc.nPc < 2 ^ 58)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hlp : EBlk H0 olp (p.lps.map Enc.idxW))
    (hpf : BlkAt H0 pp (Mc.pfvs.map Enc.idxW)) (hA : BlkAt H0 pa (Mc.ds.map Enc.idxW))
    (tele : List EIdx) (leaf : EIdx) (tb : Nat) (htb : BlkAt H0 tb (tele.map Enc.idxW ++ [Enc.idxW leaf]))
    (f : EIdx) (H : List (BitVec 64)) (hp : H0 <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (k53Params.zip [cellA C tb, BitVec.ofNat 64 tele.length, Enc.idxW leaf,
        Enc.idxW f, BitVec.ofNat 64 Mc.nPc, cellA C om, Enc.idxW Mc.lvls, cellA C olp, wty,
        cellA C pp, BitVec.ofNat 64 Mc.pfvs.length, cellA C pa, BitVec.ofNat 64 Mc.ds.length, wnm]))
      k53Body s (targetK53 mode C.fe p fts Mc tele leaf f) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (k53_none _ _) ?_
  unfold targetK53
  have hpC : C.H <+: H := hp0.trans hp
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN0 => ?_)
  have hHN0' : H.length ≤ C.HN := hHN0
  have htl : tele.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN0' (blkAt_mono htb hp); simp at this; omega
  refine specR_callNIH (C := ctxH C H) k53Sp fStripPis [pFu, pH] [vv k53Tn, vv k53F] (stripBody C fStripPis 6)
    [BitVec.ofNat 64 tele.length, Enc.idxW f] (by decide) rfl (by decide) hc.sp
    ⟨by simp +decide [sev, Env.get, k53Params, ctxEnv], by simp +decide [sev, Env.get, k53Params, ctxEnv], trivial⟩
    (PostSP (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ tys b, o = some (tys, b) → ∃ ob, w = cellA C ob ∧
      BlkAt H' ob (tys.map Enc.idxW ++ [Enc.idxW b]))
    (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (stripPis_spec C hok hc.sp tele.length (by omega) H s f))
    (fun o w s1 H1 hp1 ⟨hn, hsm⟩ => ?_)
  have hp1' : H <+: H1 := hp1
  rcases o with _ | ⟨tys, lw⟩
  · have e0 := hn rfl
    subst e0
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, rfl, hsb⟩ := hsm tys lw rfl
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hHN' : H1.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hol : ob < H1.length := (List.getElem?_eq_some_iff.mp hsb.1).1
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  have htys : tys.length < 2 ^ 61 := by have := blk_len_lt hok hHN' hsb; simp at this; omega
  have hb0 : H1[ob]? = some (BitVec.ofNat 64 (tys.length + 1)) := by simpa using hsb.1
  refine UD.specR_heapLoadI' (C := ctxH C H1) k53Wl (vv k53Sp) ob _ hb0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_assignI k53Wl _ (BitVec.ofNat 64 tys.length) (by decide)
    (by simp only [sev, sev_vv, Env.get_cons]; simp; exact ofNat_succ_sub_one tys.length) ?_
  have hlw : H1[ob + 1 + tys.length]? = some (Enc.idxW lw) := by
    have := hsb.2 tys.length (by simp)
    rw [List.getElem_append_right (by simp)] at this
    simpa using this
  refine UD.specR_heapLoadI' (C := ctxH C H1) k53Lw _ (ob + 1 + tys.length) _ hlw (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_mulIdx C ob tys.length (by omega)) ?_
  refine specR_callNIH (C := ctxH C H1) k53Ew fElm elmParams [vv k53Sp, .const 0, vv k53Wl] (elmBody C)
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 tys.length] (by decide) rfl (by decide) hc.elm.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H1)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu elmParams _ rfl hlk)
      (by have h := elm_spec (σ := σ) ra C hok hc.elm tys ob htys H1 (hpC.trans hp1') (elemsAt_of_blk hsb) tys.length 0 H1 s1
            (by omega) (by omega) (List.prefix_refl _); simp only [List.drop_zero] at h; exact h))
    (fun ew w s2 H2 hp2 ⟨oe, hw, heb⟩ => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  refine specR_callNIH (C := ctxH C H2) k53Et fElm elmParams [vv k53Tb, .const 0, vv k53Tn] (elmBody C)
    [cellA C tb, BitVec.ofNat 64 0, BitVec.ofNat 64 tele.length] (by decide) rfl (by decide) hc.elm.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], trivial⟩
    (PostA (ctxH C H2)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu elmParams _ rfl hlk)
      (by have h := elm_spec (σ := σ) ra C hok hc.elm tele tb htl H0 hp0 (elemsAt_of_blk htb) tele.length 0 H2 s2
            (by omega) (by omega) (hp.trans (hp1'.trans hp2')); simp only [List.drop_zero] at h; exact h))
    (fun et w s3 H3 hp3 ⟨ot', hw, hetb⟩ => ?_)
  subst hw
  have hp3' : H2 <+: H3 := hp3
  refine specR_callPure (C := ctxH C H3) k53Q fBlkEq beParams [vv k53Ew, vv k53Et, .const 0] beBody
    [cellA C oe, cellA C ot', BitVec.ofNat 64 0] (ew.drop 0 == et.drop 0) (by decide) rfl (by decide) hc.be
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu beParams _ rfl hlk)
      (be_spec C hok hc.be oe ot' ew et H3 s3 (blkAt_mono heb hp3') hetb ew.length 0 (by omega) (by omega)))
    (fun w H4 hp4 hw => ?_)
  subst hw
  simp only [List.drop_zero]
  by_cases hee : ew = et
  swap
  · have hb : (ew == et) = false := by simpa using hee
    rw [hb]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  subst hee
  simp only [beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  have hp4' : H3 <+: H4 := hp4
  have hpC4 : C.H <+: H4 := hpC.trans (hp1'.trans (hp2'.trans (hp3'.trans hp4')))
  refine specR_callNIM (C := ctxH C H4) k53Lh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Lw]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW lw] (by decide) rfl (by decide) hc.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel lw s3 = .ok (a, s') ∧ Post (ctxH C H4) s3 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H4) hc.gf coreWalkFuel lw s3 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun lh w s5 st ⟨_, hw, hs, _⟩ => ?_)
  subst hw; subst s5
  refine specR_callNIM (C := ctxH C H4) k53Mh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Mj]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW leaf] (by decide) rfl (by decide) hc.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel leaf s3 = .ok (a, s') ∧ Post (ctxH C H4) s3 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H4) hc.gf coreWalkFuel leaf s3 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun mh w s5 st ⟨_, hw, hs, _⟩ => ?_)
  subst hw; subst s5
  refine Knot.specR_tagIteV k53Lh lh 3 (by decide) (by decide) (by simp +decide [Env.get_cons])
    (fun htl => ?_) (fun _ => specR_hangI)
  refine Knot.specR_tagIteV k53Mh mh 3 (by decide) (by decide) (by simp +decide [Env.get_cons])
    (fun htm => ?_) (fun _ => specR_hangI)
  rw [ite_eq_left_iff.mpr (fun h => absurd (by simp [htl, htm, ETag.const]) h)]
  unfold k53Tail
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, k53Params, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv k53Lh) (Enc.idxW lh) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP lh (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htl]; rfl
  obtain ⟨I1, us1, rfl⟩ := UD.tagN_const h3
  have hvc : s3.store.viewConst lh = some (I1, us1) := ConPanqueque.T.WC.viewConst_of_view (by rw [htl]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' k53I1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW I1) (by decide)
    (by simp [sev, Env.get_cons]) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW I1) [Enc.idxW us1] []) ?_
  refine specR_loadI' k53U1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us1) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW I1) (Enc.idxW us1) [] []) ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, k53Params, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv k53Mh) (Enc.idxW mh) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP mh (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons] <;> rfl) (by decide) (fun v2 P2 hv2 htn2 _ => ?_)
  have h3' : v2.tagN = 3 := by rw [htn2, htm]; rfl
  obtain ⟨I2, us2, rfl⟩ := UD.tagN_const h3'
  have hvc2 : s3.store.viewConst mh = some (I2, us2) := ConPanqueque.T.WC.viewConst_of_view (by rw [htm]; rfl) hv2
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc2]) ?_
  dsimp only
  refine specR_loadI' k53I2 (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW I2) (by decide)
    (by simp [sev, Env.get_cons]) (by simp)
    (by simp only [encEView, Enc.encConst, List.append_nil, List.mem_append]
        exact Or.inl (wordsAt_mem0 P2 (Enc.idxW I2) [Enc.idxW us2] [])) ?_
  refine specR_callNIH (C := ctxH C H4) k53La fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Lw] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW lw] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H4)) (fun rr w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rr.map Enc.idxW))
    (fun rr w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H4 lw s3))
    (fun la w s5 H5 hp5 ⟨ola, hw, hlab⟩ => ?_)
  subst hw
  have hp5' : H4 <+: H5 := hp5
  refine specR_callNIH (C := ctxH C H5) k53Ma fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv k53Mj] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW leaf] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], trivial⟩
    (PostA (ctxH C H5)) (fun rr w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rr.map Enc.idxW))
    (fun rr w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H5 leaf s5))
    (fun ma w s6 H6 hp6 ⟨oma, hw, hmab⟩ => ?_)
  subst hw
  have hp6' : H5 <+: H6 := hp6
  have hlab6 := blkAt_mono hlab hp6'
  have hlal := hlab6.1
  simp only [List.length_map] at hlal
  have hmal := hmab.1
  simp only [List.length_map] at hmal
  refine UD.specR_heapLoadI' (C := ctxH C H6) k53Ll (vv k53La) ola _ hlal (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H6) k53Ml (vv k53Ma) oma _ hmal (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN6 => ?_)
  have hHN6' : H6.length ≤ C.HN := hHN6
  have hlal' : la.length < 2 ^ 61 := by have := blk_len_lt hok hHN6' hlab6; simpa using this
  have hmal' : ma.length < 2 ^ 61 := by have := blk_len_lt hok hHN6' hmab; simpa using this
  by_cases hII : I1 = I2
  swap
  · have hne : Enc.idxW I1 ≠ Enc.idxW I2 := fun e => hII (Enc.idxW_inj e)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  subst hII
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  by_cases hLL : la.length = ma.length
  swap
  · have hne : BitVec.ofNat 64 la.length ≠ BitVec.ofNat 64 ma.length := fun e => hLL (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hLL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  rw [show (la.length == ma.length) = true from by simp [hLL]]
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false]
  have hlwn := nd_lt_iff la.length Mc.nPc (by omega) (by omega)
  by_cases hnl : Mc.nPc ≤ la.length
  swap
  · exact specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, k53Params, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwn.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, k53Params, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hpC6 : C.H <+: H6 := hpC4.trans (hp5'.trans hp6')
  refine specR_callNIH (C := ctxH C H6) k53Le fElm elmParams [vv k53La, vv k53Npc, vv k53Ll] (elmBody C)
    [cellA C ola, BitVec.ofNat 64 Mc.nPc, BitVec.ofNat 64 la.length] (by decide) rfl (by decide) hc.elm.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H6)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu elmParams _ rfl hlk)
      (elm_spec (σ := σ) ra C hok hc.elm la ola hlal' H6 hpC6 (elemsAt_of_blk (ys := []) (by simpa using hlab6))
        (la.length - Mc.nPc) Mc.nPc H6 s6 rfl hnl (List.prefix_refl _)))
    (fun le w s7 H7 hp7 ⟨ole, hw, hleb⟩ => ?_)
  subst hw
  have hp7' : H6 <+: H7 := hp7
  refine specR_callNIH (C := ctxH C H7) k53Me fElm elmParams [vv k53Ma, vv k53Npc, vv k53Ml] (elmBody C)
    [cellA C oma, BitVec.ofNat 64 Mc.nPc, BitVec.ofNat 64 ma.length] (by decide) rfl (by decide) hc.elm.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H7)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu elmParams _ rfl hlk)
      (elm_spec (σ := σ) ra C hok hc.elm ma oma hmal' H6 hpC6 (elemsAt_of_blk (ys := []) (by simpa using hmab))
        (ma.length - Mc.nPc) Mc.nPc H7 s7 rfl (by omega) hp7'))
    (fun me w s8 H8 hp8 ⟨ome, hw, hmeb⟩ => ?_)
  subst hw
  have hp8' : H7 <+: H8 := hp8
  refine specR_callPure (C := ctxH C H8) k53Q fBlkEq beParams [vv k53Le, vv k53Me, .const 0] beBody
    [cellA C ole, cellA C ome, BitVec.ofNat 64 0] (le.drop 0 == me.drop 0) (by decide) rfl (by decide) hc.be
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostB (ctxH C H8)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu beParams _ rfl hlk)
      (be_spec C hok hc.be ole ome le me H8 s8 (blkAt_mono hleb hp8') hmeb le.length 0 (by omega) (by omega)))
    (fun w H9 hp9 hw => ?_)
  subst hw
  simp only [List.drop_zero]
  by_cases hlm : le = me
  swap
  · have hb : (le == me) = false := by simpa using hlm
    rw [hb]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  subst hlm
  simp only [beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true, ite_false]
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  have hp9' : H8 <+: H9 := hp9
  have hp69 : H6 <+: H9 := hp7'.trans (hp8'.trans hp9')
  refine specR_callPure (C := ctxH C H9) k53Lp fTkb tkbParams [vv k53La, .const 0, vv k53Npc] (tkbBody C)
    [cellA C ola, BitVec.ofNat 64 0, BitVec.ofNat 64 Mc.nPc] ((la.take Mc.nPc).drop 0) (by decide) rfl (by decide) hc.tkb
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], trivial⟩
    (PostA (ctxH C H9)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tkbParams _ rfl hlk)
      (tkb_spec C hok hc.tkb la ola Mc.nPc hnl hlal' H6 hpC6 (elemsAt_of_blk (ys := []) (by simpa using hlab6))
        Mc.nPc 0 H9 s8 (by omega) (by omega) hp69))
    (fun w H10 hp10 ⟨olp', hw, hlpb⟩ => ?_)
  subst hw
  simp only [List.drop_zero] at hlpb
  have hp10' : H9 <+: H10 := hp10
  have hlpl' : (la.take Mc.nPc).length = Mc.nPc := by simp; omega
  refine ILP.callE_spec (C := ctxH C H10) k53Hd fInternConst [lEn, lEus] [vv k53I1, vv k53U1] constBody
    [Enc.idxW I1, Enc.idxW us1] (by decide) rfl (by decide) hc.ic
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (const_body_spec ra (ctxH C H10) (ctxOK_H hok H10) s8 _ _) (fun hd s9 => ?_)
  refine ILP.callE_spec (C := ctxH C H10) k53Ap ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv k53Hd, vv k53Lp, .const 0, vv k53Npc] ExK.mkaBody
    [Enc.idxW hd, cellA C olp', BitVec.ofNat 64 0, BitVec.ofNat 64 (la.take Mc.nPc).length] (by decide) rfl (by decide)
    hc.mka
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv, hlpl'], trivial⟩
    (by have h := ExK.mkAppN_spec (σ := σ) ra (ctxH C H10) (ctxOK_H hok H10) hc.mka hc.app olp' (la.take Mc.nPc) hlpb
          (by omega) 0 (by omega) hd s9; simp only [List.drop_zero] at h; exact h)
    (fun app s10 => ?_)
  have hpC10 : C.H <+: H10 := hpC6.trans (hp69.trans hp10')
  refine specR_callNIH (C := ctxH C H10) k53O fNocTop ntParams [vv k53Ap, vv k53Ms, .const 0, .const 0] ntBody
    [Enc.idxW app, cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.nt.top
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], rfl, rfl,
      trivial⟩
    (PostB (ctxH C H10)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
      (by simp only [BlockShape.memberNames]
          exact nt_spec C hok hc.nt p.members om hM (by omega) 0 0 (by decide) (by decide) app H10 s10 hpC10))
    (fun b wb s11 H11 hp11 hw => ?_)
  subst hw
  have hp11' : H10 <+: H11 := hp11
  cases b
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  have hpH11 : H <+: H11 := hp1'.trans (hp2'.trans (hp3'.trans (hp4'.trans (hp5'.trans (hp6'.trans (hp69.trans
    (hp10'.trans hp11')))))))
  refine specR_congr (m' := targetClassMatch mode C.fe p fts Mc.pfvs Mc.lvls Mc.ds us1 (la.take Mc.nPc) >>=
    fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H11) k53R fTcc tccParams
    [vv k53Us, vv k53U1, vv k53Olp, vv k53Ms, vv k53Pp, vv k53Pn, vv k53Pa, vv k53Lp, vv k53Nd] (tccBody C)
    [Enc.idxW Mc.lvls, Enc.idxW us1, cellA C olp, cellA C om, cellA C pp, BitVec.ofNat 64 Mc.pfvs.length,
      cellA C pa, cellA C olp', BitVec.ofNat 64 Mc.ds.length] (by decide) rfl (by decide) hc.tcc.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, k53Params, ctxEnv],
      trivial⟩
    (PostB (ctxH C H11)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tccParams _ rfl hlk)
      (tcc_spec mode ra C hok hs hc.tcc p fts hfts Mc.pfvs Mc.ds
        (la.take Mc.nPc) Mc.lvls us1 olp om pp pa olp' hlpl
        hdl (by omega) hpl hml H11 (hpC10.trans hp11')
        (eblk_mono hlp (hp.trans hpH11))
        (ptrsRep_mono (hpC10.trans hp11') (fun _ _ h => memberRep_mono (hpC10.trans hp11') h) hM) (blkAt_mono hpf (hp.trans hpH11))
        (blkAt_mono hA (hp.trans hpH11)) (blkAt_mono hlpb hp11') s11))
    (fun r wr s12 H12 hp12 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H12, hpH11.trans hp12, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classNodesAgree` over a class's table, at one constructor -/

def cndT := ofString "cnd_t"
def cndJ := ofString "cnd_j"
def cndK := ofString "cnd_k"
def cndCn := ofString "cnd_cn"
def cndFv := ofString "cnd_fv"
def cndFn := ofString "cnd_fn"
def cndI := ofString "cnd_i"
def cndP := ofString "cnd_p"
def cndX := ofString "cnd_x"
def cndTy := ofString "cnd_ty"
def cndD := ofString "cnd_d"
def cndDl := ofString "cnd_dl"
def cndF := ofString "cnd_f"
def cndR := ofString "cnd_r"
def fCnd := ofString "classNodesAgree"

/-- `k53`'s fixed arguments: the telescope block, its length, the leaf, then (after the field) the class's. -/
def cndParams : List MlS := [cndT, cndJ, cndK, cndCn, cndFv, cndFn, cndI, k53Tb, k53Tn, k53Mj, k53Npc, k53Ms, k53Us,
  k53Olp, k53Ty0, k53Pp, k53Pn, k53Pa, k53Nd, k53Nm]
def cndLocals : List MlS := [cndP, cndX, cndTy, cndD, cndDl, cndF, cndR]

def cndRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, cndR), none)) fCnd [vv cndT, .op .add [vv cndJ, .const 1], vv cndK, vv cndCn,
      vv cndFv, vv cndFn, vv cndI, vv k53Tb, vv k53Tn, vv k53Mj, vv k53Npc, vv k53Ms, vv k53Us, vv k53Olp, vv k53Ty0,
      vv k53Pp, vv k53Pn, vv k53Pa, vv k53Nd, vv k53Nm])
    (.return (.const 0))

def cndBody : ProgHOL 64 := prologue cndLocals
  (.ite (.cmp .lower (vv cndJ) (vv cndK))
    (.seq (.assign .local cndP (.load .one (.op .add [vv cndT, .op .add [.panop .mul [vv cndJ, .const 8], .const 8]])))
    (.seq (.assign .local cndX (.load .one (vv cndP)))
    (.ite (.cmp .equal (vv cndX) (vv cndCn))
      (.seq (.assign .local cndTy (.load .one (.op .add [vv cndP, .const 24])))
      (.seq (.call (some (some (.local, cndD), none)) fTpw [vv cndFv, .const 0, vv cndFn, vv cndTy])
      (.seq (.assign .local cndDl (.load .one (vv cndD)))
      (.ite (.cmp .lower (vv cndI) (vv cndDl))
        (.seq (.assign .local cndF (.load .one (.op .add [vv cndD, .op .add [.panop .mul [vv cndI, .const 8], .const 8]])))
        (.seq (.call (some (some (.local, cndR), none)) fK53 [vv k53Tb, vv k53Tn, vv k53Mj, vv cndF, vv k53Npc, vv k53Ms,
            vv k53Us, vv k53Olp, vv k53Ty0, vv k53Pp, vv k53Pn, vv k53Pa, vv k53Nd, vv k53Nm])
        (.ite (.cmp .equal (vv cndR) (.const 0)) hang cndRec)))
        hang))))
      cndRec)))
    (.return (.const 0)))

structure CNDCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  tpw : TPWCodes C
  k53 : K53Codes mode C
  self : C.code.lookup fCnd = some (cndParams.map (fun p => (p, ShapeHOL.one)), cndBody, .one)

section
variable {σ : Type}

theorem cnd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cndLocals → (ctxEnv C ++ cndParams.zip vals).get x = none :=
  Knot.params_none C cndLocals cndParams vals (by decide) (by decide)

set_option maxHeartbeats 64000000 in
/-- **`classNodesAgree`** over the table's entries of constructor `cn` from entry `j` on. -/
theorem cnd_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CNDCodes mode C) (p : BlockShape) (fts : List EIdx) (hfts : fts = p.formers.map (·.type)) (hml : p.members.length < 2 ^ 58)
    (wty wnm : BitVec 64)
    (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (Mc : TargetMajor) (olp pp pa : Nat) (hlpl : p.lps.length < 2 ^ 59) (hdl : Mc.ds.length < 2 ^ 58)
    (hpl : Mc.pfvs.length < 2 ^ 58) (hnpc : Mc.nPc < 2 ^ 58)
    (tbl : List NestCtorNf) (ot : Nat) (htl : tbl.length < 2 ^ 58) (cn : NIdx)
    (fvs : List EIdx) (pv : Nat) (hfl : fvs.length < 2 ^ 56) (i : Nat) (hi : i < 2 ^ 56)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hlp : EBlk H0 olp (p.lps.map Enc.idxW))
    (hpf : BlkAt H0 pp (Mc.pfvs.map Enc.idxW)) (hA : BlkAt H0 pa (Mc.ds.map Enc.idxW))
    (htb : PRep C H0 ot (fun H o nf => NfRep C H o nf) tbl) (hfb : BlkAt H0 pv (fvs.map Enc.idxW))
    (tele : List EIdx) (leaf : EIdx) (tb : Nat) (htlb : BlkAt H0 tb (tele.map Enc.idxW ++ [Enc.idxW leaf])) :
    ∀ f j (H : List (BitVec 64)) (s : AState), tbl.length - j = f → j ≤ tbl.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cndParams.zip [cellA C ot, BitVec.ofNat 64 j, BitVec.ofNat 64 tbl.length,
        Enc.idxW cn, cellA C pv, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 i, cellA C tb,
        BitVec.ofNat 64 tele.length, Enc.idxW leaf, BitVec.ofNat 64 Mc.nPc, cellA C om, Enc.idxW Mc.lvls, cellA C olp,
        wty, cellA C pp, BitVec.ofNat 64 Mc.pfvs.length, cellA C pa, BitVec.ofNat 64 Mc.ds.length,
        wnm])) cndBody s
        (classNodesAgree mode C.fe p fts Mc tele leaf fvs i ((tbl.drop j).filter (·.ctor == cn)))
        (Decl.PostU (ctxH C H)) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := htb
  have hpost : ∀ (H : List (BitVec 64)) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      Decl.PostU (ctxH C H) a w s' st → Decl.PostU (ctxH C H) a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨H', hp', hsr⟩ => ⟨H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro j H s hf hj hp
    have hin : j = tbl.length := by omega
    subst hin
    refine specR_prologue (hpost H) (cnd_none _ _) ?_
    have hlw := nd_lt_iff tbl.length tbl.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cndParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hf hj hp
    have hin : j < tbl.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (hpost H) (cnd_none _ _) ?_
    have hlw := nd_lt_iff j tbl.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cndParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : j < os.length := by omega
    have hpe := hosb.2 j (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hnf := nfRep_mono hp (hosr j hin hio)
    refine UD.specR_heapLoadI' (C := ctxH C H) cndP _ (ot + 1 + j) _ (get_prefix hpe hp) (by decide)
      (by simp +decide [sev, Env.get, cndParams, ctxEnv]; exact cellA_mulIdx C ot j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cndX (vv cndP) _ _ hnf.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.filter_cons]
    -- the recursive call on the rest
    have hrec : ∀ (Hr : List (BitVec 64)) (sr : AState) (Γ : Env), H <+: Hr →
        Γ = ((cndX, Enc.idxW tbl[j].ctor) :: (cndP, cellA C os[j]) :: (ctxEnv (ctxH C H) ++ cndParams.zip
          [cellA C ot, BitVec.ofNat 64 j, BitVec.ofNat 64 tbl.length, Enc.idxW cn, cellA C pv,
            BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 i, cellA C tb, BitVec.ofNat 64 tele.length, Enc.idxW leaf,
            BitVec.ofNat 64 Mc.nPc, cellA C om, Enc.idxW Mc.lvls, cellA C olp, wty, cellA C pp,
            BitVec.ofNat 64 Mc.pfvs.length, cellA C pa, BitVec.ofNat 64 Mc.ds.length, wnm])) →
        ∀ (Γ' : Env) (M : Mem), (∀ x, x ∈ cndParams → Γ'.get x = Γ.get x) →
        SpecR (σ := σ) (Inv (ctxH C Hr) sr Γ' M (ctxLocals ++ cndLocals)) cndRec sr
          (classNodesAgree mode C.fe p fts Mc tele leaf fvs i ((tbl.drop (j + 1)).filter (·.ctor == cn)))
          (Decl.PostU (ctxH C H)) := by
      intro Hr sr Γ hpr eΓ Γ' M hΓ
      subst eΓ
      have g : ∀ x, x ∈ cndParams → Γ'.get x = _ := hΓ
      refine specR_congr (m' := classNodesAgree mode C.fe p fts Mc tele leaf fvs i
        ((tbl.drop (j + 1)).filter (·.ctor == cn)) >>= fun _ => pure ()) (by simp) ?_
      unfold cndRec
      refine specR_callNIH (C := ctxH C Hr) cndR fCnd cndParams [vv cndT, .op .add [vv cndJ, .const 1], vv cndK, vv cndCn,
          vv cndFv, vv cndFn, vv cndI, vv k53Tb, vv k53Tn, vv k53Mj, vv k53Npc, vv k53Ms, vv k53Us, vv k53Olp, vv k53Ty0,
          vv k53Pp, vv k53Pn, vv k53Pa, vv k53Nd, vv k53Nm] cndBody
        [cellA C ot, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 tbl.length, Enc.idxW cn, cellA C pv,
            BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 i, cellA C tb, BitVec.ofNat 64 tele.length, Enc.idxW leaf,
            BitVec.ofNat 64 Mc.nPc, cellA C om, Enc.idxW Mc.lvls, cellA C olp, wty, cellA C pp,
            BitVec.ofNat 64 Mc.pfvs.length, cellA C pa, BitVec.ofNat 64 Mc.ds.length, wnm]
        (by decide) rfl (by decide) hc.self
        ⟨by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv]; exact word_add1_eq j,
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cndParams, ctxEnv],
          trivial⟩
        (Decl.PostU (ctxH C Hr)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cndParams _ rfl hlk)
          (ih (j + 1) Hr sr (by omega) (by omega) (hp.trans hpr)))
        (fun _ w s3 H3 hp3 _ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hpr.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    by_cases he : tbl[j].ctor = cn
    swap
    · have hne : Enc.idxW tbl[j].ctor ≠ Enc.idxW cn := fun e => he (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
      have hbe : (tbl[j].ctor == cn) = false := beq_eq_false_iff_ne.mpr he
      simp only [hbe, Bool.false_eq_true, ↓reduceIte]
      exact hrec H s _ (List.prefix_refl _) rfl _ _ (fun x _ => rfl)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [he, beq_self_eq_true, ↓reduceIte]
    unfold classNodesAgree
    refine UD.specR_heapLoadI' (C := ctxH C H) cndTy _ (os[j] + 3) _ hnf.2.2.2 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C os[j] 3) ?_
    refine specR_callNIH (C := ctxH C H) cndD fTpw tpwParams [vv cndFv, .const 0, vv cndFn, vv cndTy] (tpwBody C)
      [cellA C pv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, Enc.idxW tbl[j].ty] (by decide) rfl (by decide) hc.tpw.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSL (ctxH C H)) (fun o w _ H' => ∃ ds ow, o = some ds ∧ w = cellA C ow ∧ BlkAt H' ow (ds.map Enc.idxW))
      (fun o w s' st ⟨ds, H', ow, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ow, h0, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tpwParams _ rfl hlk)
        (by have h := tpw_spec (σ := σ) ra C hok hc.tpw fvs pv H0 hp0 hfb fvs.length 0 H s tbl[j].ty (by omega) (by omega)
              hp; simp only [List.drop_zero] at h; exact h))
      (fun o w s1 H1 hp1 ⟨ds, ow, ho, hw, hdb⟩ => ?_)
    subst ho hw
    have hp1' : H <+: H1 := hp1
    simp only [Option.getD_some]
    have hdl1 := hdb.1
    simp only [List.length_map] at hdl1
    refine UD.specR_heapLoadI' (C := ctxH C H1) cndDl (vv cndD) ow _ hdl1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hdsl : ds.length < 2 ^ 61 := by have := blk_len_lt hok hHN1' hdb; simpa using this
    have hlwi := nd_lt_iff i ds.length (by omega) (by omega)
    by_cases hid : i < ds.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cndParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h)
        (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cndParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwi.mpr hid]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.getElem?_eq_getElem hid]
    simp only
    have hdi := hdb.2 i (by simp; omega)
    simp only [List.getElem_map] at hdi
    refine UD.specR_heapLoadI' (C := ctxH C H1) cndF _ (ow + 1 + i) _ hdi (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv]; exact cellA_mulIdx C ow i (by omega)) ?_
    refine specR_callNIH (C := ctxH C H1) cndR fK53 k53Params [vv k53Tb, vv k53Tn, vv k53Mj, vv cndF, vv k53Npc, vv k53Ms,
        vv k53Us, vv k53Olp, vv k53Ty0, vv k53Pp, vv k53Pn, vv k53Pa, vv k53Nd, vv k53Nm] k53Body
      [cellA C tb, BitVec.ofNat 64 tele.length, Enc.idxW leaf, Enc.idxW ds[i], BitVec.ofNat 64 Mc.nPc, cellA C om,
        Enc.idxW Mc.lvls, cellA C olp, wty, cellA C pp, BitVec.ofNat 64 Mc.pfvs.length, cellA C pa,
        BitVec.ofNat 64 Mc.ds.length, wnm] (by decide) rfl (by decide) hc.k53.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cndParams, ctxEnv],
        trivial⟩
      (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu k53Params _ rfl hlk)
        (k53_spec mode ra C hok hs hc.k53 p fts hfts hml wty wnm om hM Mc olp pp pa hlpl hdl hpl hnpc H0 hp0 hlp hpf hA tele leaf tb
          htlb ds[i] H1 (hp.trans hp1') s1))
      (fun b wb s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    cases b
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true]
    exact hrec H2 s2 _ (hp1'.trans hp2') rfl _ _ (fun x hx => by
      simp only [cndParams, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)

end

/-! ## `classFieldsAgree` over the kinds block -/

def cfgKb := ofString "cfg_kb"
def cfgI := ofString "cfg_i"
def cfgN := ofString "cfg_n"
def cfgK := ofString "cfg_k"
def cfgX := ofString "cfg_x"
def cfgFt := ofString "cfg_ft"
def cfgSb := ofString "cfg_sb"
def cfgWl := ofString "cfg_wl"
def cfgLf := ofString "cfg_lf"
def cfgHd := ofString "cfg_hd"
def cfgNm := ofString "cfg_nm"
def cfgR := ofString "cfg_r"
def cfgOms := ofString "cfg_oms"
def cfgNcl := ofString "cfg_ncl"
def cfgC := ofString "cfg_c"
def cfgQ := ofString "cfg_q"
def cfgOa := ofString "cfg_oa"
def fCfg := ofString "classFieldsAgree"

def cfgParams : List MlS := [cfgKb, cfgI, cfgN, cndFv, cndFn, cndT, cndK, cndCn, cfgOms, cfgNcl, k53Ms, k53Olp,
  k53Ty0, k53Pp, k53Pn, k53Nm]
def cfgLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, cfgX, cfgFt, cfgSb, cfgWl, cfgLf, cfgHd, cfgNm, cfgR,
  cfgC, cfgQ, cfgOa, cfgK, k53Npc, k53Us, k53Pa, k53Nd]

def cfgRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, cfgR), none)) fCfg [vv cfgKb, .op .add [vv cfgI, .const 1], vv cfgN, vv cndFv,
      vv cndFn, vv cndT, vv cndK, vv cndCn, vv cfgOms, vv cfgNcl, vv k53Ms, vv k53Olp, vv k53Ty0, vv k53Pp,
      vv k53Pn, vv k53Nm])
    (.return (.const 0))

def cfgBody : ProgHOL 64 := prologue cfgLocals
  (.ite (.cmp .lower (vv cfgI) (vv cfgN))
    (.seq (.assign .local cfgX (.load .one (.op .add [vv cfgKb, .op .add [.panop .mul [vv cfgI, .const 8], .const 8]])))
    (.ite (.cmp .equal (vv cfgX) (.const 0)) cfgRec
    (.seq (.assign .local cfgC (.shift .lsr (vv cfgX) (.const 32)))
    (.ite (.cmp .lower (vv cfgC) (vv cfgNcl))
    (.seq (.assign .local cfgX (.op .sub [.op .and [vv cfgX, .const (BitVec.ofNat 64 (2 ^ 32 - 1))], .const 1]))
    (.seq (.assign .local cfgQ (.load .one (.op .add [vv cfgOms, .op .add [.panop .mul [vv cfgC, .const 8], .const 8]])))
    (.seq (.assign .local cfgOa (.load .one (.op .add [vv cfgQ, .const 24])))
    (.seq (.assign .local cfgK (.load .one (vv cfgOa)))
    (.seq (.assign .local k53Us (.load .one (.op .add [vv cfgOa, .const 8])))
    (.seq (.assign .local k53Pa (.load .one (.op .add [vv cfgOa, .const 16])))
    (.seq (.assign .local k53Nd (.load .one (vv k53Pa)))
    (.seq (.assign .local k53Npc (.load .one (.op .add [vv cfgOa, .const 24])))
    (guardP k53Npc 58 (guardP k53Nd 58 (.ite (.cmp .lower (vv cfgI) (vv cndFn))
    (.seq (.assign .local cfgFt (.load .one (.op .add [vv cndFv, .op .add [.panop .mul [vv cfgI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, cfgFt), none)) fFvt [vv cfgFt])
    (.seq (.call (some (some (.local, cfgSb), none)) fStripPis [vv cfgX, vv cfgFt])
    (.ite (.cmp .equal (vv cfgSb) (.const 0)) hang
    (.seq (.assign .local cfgWl (.load .one (vv cfgSb)))
    (.seq (.assign .local cfgWl (.op .sub [vv cfgWl, .const 1]))
    (.seq (.assign .local cfgLf (.load .one (.op .add [vv cfgSb, .op .add [.panop .mul [vv cfgWl, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, cfgHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv cfgLf])
    (.ite (tagIsE cfgHd 3)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv cfgHd)) (.seq eViewP
      (.seq (.assign .local cfgNm (.load .one (vv lRp)))
      (.ite (.cmp .equal (vv cfgNm) (vv cfgK))
        (.seq (.call (some (some (.local, cfgR), none)) fCnd [vv cndT, .const 0, vv cndK, vv cndCn, vv cndFv, vv cndFn,
            vv cfgI, vv cfgSb, vv cfgWl, vv cfgLf, vv k53Npc, vv k53Ms, vv k53Us, vv k53Olp, vv k53Ty0, vv k53Pp,
            vv k53Pn, vv k53Pa, vv k53Nd, vv k53Nm])
          cfgRec)
        hang)))))
      hang)))))))))
    hang)))))))))))
    hang))))
    (.return (.const 0)))

structure CFGCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  fvt : C.code.lookup fFvt = some ([(pH, .one)], ExM.fvtBody, .one)
  cnd : CNDCodes mode C
  self : C.code.lookup fCfg = some (cfgParams.map (fun p => (p, ShapeHOL.one)), cfgBody, .one)

section
variable {σ : Type}

theorem cfg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfgLocals → (ctxEnv C ++ cfgParams.zip vals).get x = none :=
  Knot.params_none C cfgLocals cfgParams vals (by decide) (by decide)

set_option maxHeartbeats 64000000 in
/-- **`classFieldsAgree`** over the class block `ms` from field `i` on (the kinds a block of `cfKindW`s; a field's
class is read off its kinds word, a class past the block hangs). -/
theorem cfg_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CFGCodes mode C) (p : BlockShape) (fts : List EIdx) (hfts : fts = p.formers.map (·.type))
    (hml : p.members.length < 2 ^ 58) (wty wnm : BitVec 64)
    (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (ms : List TargetMajor) (oms : Nat) (pfvs : List EIdx) (hpfv : ∀ m ∈ ms, m.pfvs = pfvs) (hmsl : ms.length < 2 ^ 58)
    (olp pp : Nat) (hlpl : p.lps.length < 2 ^ 59) (hpl : pfvs.length < 2 ^ 58)
    (tbl : List NestCtorNf) (ot : Nat) (htl : tbl.length < 2 ^ 58) (cn : NIdx)
    (fvs : List EIdx) (pv : Nat) (hfl : fvs.length < 2 ^ 56)
    (ks : List ClassField) (pk : Nat) (hko : KindsOK ks) (hkl : ks.length < 2 ^ 56)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hlp : EBlk H0 olp (p.lps.map Enc.idxW))
    (hpf : BlkAt H0 pp (pfvs.map Enc.idxW)) (hT : TMBlkR C H0 oms ms)
    (htb : PRep C H0 ot (fun H o nf => NfRep C H o nf) tbl) (hfb : BlkAt H0 pv (fvs.map Enc.idxW))
    (hkb : BlkAt H0 pk (ks.map cfKindW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), ks.length - i = f → i ≤ ks.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cfgParams.zip [cellA C pk, BitVec.ofNat 64 i, BitVec.ofNat 64 ks.length,
        cellA C pv, BitVec.ofNat 64 fvs.length, cellA C ot, BitVec.ofNat 64 tbl.length, Enc.idxW cn, cellA C oms,
        BitVec.ofNat 64 ms.length, cellA C om, cellA C olp, wty, cellA C pp, BitVec.ofNat 64 pfvs.length, wnm])) cfgBody s
        (classFieldsAgree mode C.fe p fts ms fvs (tbl.filter (·.ctor == cn)) i (ks.drop i))
        (Decl.PostU (ctxH C H)) := by
  have hpost : ∀ (H : List (BitVec 64)) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      Decl.PostU (ctxH C H) a w s' st → Decl.PostU (ctxH C H) a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨H', hp', hsr⟩ => ⟨H', hp', sr_of_eq hsr rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = ks.length := by omega
    subst hin
    refine specR_prologue (hpost H) (cfg_none _ _) ?_
    have hlw := nd_lt_iff ks.length ks.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cfgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < ks.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (hpost H) (cfg_none _ _) ?_
    have hlw := nd_lt_iff i ks.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cfgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hkx := hkb.2 i (by simp; omega)
    simp only [List.getElem_map] at hkx
    refine UD.specR_heapLoadI' (C := ctxH C H) cfgX _ (pk + 1 + i) _ (get_prefix hkx hp) (by decide)
      (by simp +decide [sev, Env.get, cfgParams, ctxEnv]; exact cellA_mulIdx C pk i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin]
    -- the recursive call on the rest
    have hrec : ∀ (Hr : List (BitVec 64)) (sr : AState) (Γ' : Env) (M : Mem), H <+: Hr →
        (∀ x, x ∈ cfgParams → Γ'.get x = (ctxEnv (ctxH C H) ++ cfgParams.zip [cellA C pk, BitVec.ofNat 64 i,
          BitVec.ofNat 64 ks.length, cellA C pv, BitVec.ofNat 64 fvs.length, cellA C ot, BitVec.ofNat 64 tbl.length,
          Enc.idxW cn, cellA C oms, BitVec.ofNat 64 ms.length, cellA C om, cellA C olp, wty, cellA C pp,
          BitVec.ofNat 64 pfvs.length, wnm]).get x) →
        SpecR (σ := σ) (Inv (ctxH C Hr) sr Γ' M (ctxLocals ++ cfgLocals)) cfgRec sr
          (classFieldsAgree mode C.fe p fts ms fvs (tbl.filter (·.ctor == cn)) (i + 1) (ks.drop (i + 1)))
          (Decl.PostU (ctxH C H)) := by
      intro Hr sr Γ' M hpr g
      refine specR_congr (m' := classFieldsAgree mode C.fe p fts ms fvs (tbl.filter (·.ctor == cn)) (i + 1)
        (ks.drop (i + 1)) >>= fun _ => pure ()) (by simp) ?_
      unfold cfgRec
      refine specR_callNIH (C := ctxH C Hr) cfgR fCfg cfgParams [vv cfgKb, .op .add [vv cfgI, .const 1], vv cfgN, vv cndFv,
          vv cndFn, vv cndT, vv cndK, vv cndCn, vv cfgOms, vv cfgNcl, vv k53Ms, vv k53Olp, vv k53Ty0, vv k53Pp,
          vv k53Pn, vv k53Nm] cfgBody
        [cellA C pk, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ks.length, cellA C pv, BitVec.ofNat 64 fvs.length,
          cellA C ot, BitVec.ofNat 64 tbl.length, Enc.idxW cn, cellA C oms, BitVec.ofNat 64 ms.length, cellA C om,
          cellA C olp, wty, cellA C pp, BitVec.ofNat 64 pfvs.length, wnm]
        (by decide) rfl (by decide) hc.self
        ⟨by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv]; exact word_add1_eq i,
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          by simp only [sev, sev_vv]; rw [g _ (by decide)]; simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv],
          trivial⟩
        (Decl.PostU (ctxH C Hr)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfgParams _ rfl hlk)
          (ih (i + 1) Hr sr (by omega) (by omega) (hp.trans hpr)))
        (fun _ w s3 H3 hp3 _ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hpr.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rcases hko ks[i] (List.getElem_mem hin) with hk | ⟨c, tele, hk, htele, hc24⟩
    · rw [hk] at hkx ⊢
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, cfKindW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [classFieldsAgree]
      exact hrec H s _ _ (List.prefix_refl _) (fun x hx => by
        simp only [cfgParams, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    rw [hk] at hkx ⊢
    have hkw : cfKindW (.recursive c tele) ≠ 0 := by
      simp only [cfKindW]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hkw)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI cfgC _ (BitVec.ofNat 64 c) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp only [cfKindW]; rw [← kindW_cls c tele htele hc24]; rfl) ?_
    have hlwc := nd_lt_iff c ms.length (by omega) (by omega)
    by_cases hcl : c < ms.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cfgParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cfgParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwc.mpr hcl]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI cfgX _ (BitVec.ofNat 64 tele) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp only [cfKindW]; rw [← kindW_tele c tele htele hc24]; rfl) ?_
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN1 => ?_)
    have hHN1' : H.length ≤ C.HN := hHN1
    obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hT
    obtain ⟨op, hop, hrep⟩ := hpsr c hcl
    have hq := hpsb.2 c (by simp; omega)
    simp only [List.getElem_map] at hq
    have hpi : ps[c]'(by omega) = op := by
      rw [List.getElem?_eq_getElem (by omega)] at hop; exact Option.some.inj hop
    rw [hpi] at hq
    obtain ⟨oa, ha3, hind, hlv, ⟨od, hod, hdb⟩, hnpcE, -, -, -, -⟩ := hrep
    have hpfc : ms[c].pfvs = pfvs := hpfv _ (List.getElem_mem hcl)
    refine UD.specR_heapLoadI' (C := ctxH C H) cfgQ _ (oms + 1 + c) _ (get_prefix hq hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv]; exact cellA_mulIdx C oms c (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cfgOa _ (op + 3) _ (get_prefix ha3 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cfgK (vv cfgOa) oa _ (get_prefix hind hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) k53Us _ (oa + 1) _ (get_prefix hlv hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oa) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) k53Pa _ (oa + 2) _ (get_prefix hod hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oa 2) ?_
    have hdl0 := hdb.1
    simp only [List.length_map] at hdl0
    refine UD.specR_heapLoadI' (C := ctxH C H) k53Nd (vv k53Pa) od _ (get_prefix hdl0 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) k53Npc _ (oa + 3) _ (get_prefix hnpcE.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oa 3) ?_
    have hdl61 : ms[c].ds.length < 2 ^ 61 := by
      have := blk_len_lt hok hHN1' (blkAt_mono hdb hp); simp at this; omega
    refine specR_guardI k53Npc ms[c].nPc 58 (by decide) (by simp [Env.get_cons]) (by have := hnpcE.2; omega)
      (fun hnpc => ?_)
    refine specR_guardI k53Nd ms[c].ds.length 58 (by decide) (by simp +decide [Env.get_cons]) (by omega)
      (fun hdl => ?_)
    simp only [classFieldsAgree]
    have hlwf := nd_lt_iff i fvs.length (by omega) (by omega)
    by_cases hif : i < fvs.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cfgParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cfgParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwf.mpr hif]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hfx := hfb.2 i (by simp; omega)
    simp only [List.getElem_map] at hfx
    refine UD.specR_heapLoadI' (C := ctxH C H) cfgFt _ (pv + 1 + i) _ (get_prefix hfx hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv]; exact cellA_mulIdx C pv i (by omega)) ?_
    simp only [exprGetD, List.getElem?_eq_getElem hif]
    simp only [pure_bind]
    refine ILP.callE_spec (C := ctxH C H) cfgFt fFvt [pH] [vv cfgFt] ExM.fvtBody [Enc.idxW fvs[i]] (by decide) rfl
      (by decide) hc.fvt ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (ExM.fvt_spec (ctxH C H) s fvs[i]) (fun fty s1 => ?_)
    refine specR_callNIH (C := ctxH C H) cfgSb fStripPis [pFu, pH] [vv cfgX, vv cfgFt] (stripBody C fStripPis 6)
      [BitVec.ofNat 64 tele, Enc.idxW fty] (by decide) rfl (by decide) hc.cnd.k53.sp
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (PostSP (ctxH C H)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ tys b, o = some (tys, b) → ∃ ob, w = cellA C ob ∧
        BlkAt H' ob (tys.map Enc.idxW ++ [Enc.idxW b]))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (stripPis_spec C hok hc.cnd.k53.sp tele (by omega) H s1 fty))
      (fun o w s2 H2 hp2 ⟨hn, hsm⟩ => ?_)
    have hp2' : H <+: H2 := hp2
    rcases o with _ | ⟨tys, lf⟩
    · have e0 := hn rfl
      subst e0
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    obtain ⟨ob, rfl, hsb⟩ := hsm tys lf rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
    have hHN' : H2.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hol : ob < H2.length := (List.getElem?_eq_some_iff.mp hsb.1).1
    have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only
    have htys : tys.length < 2 ^ 61 := by have := blk_len_lt hok hHN' hsb; simp at this; omega
    have hb0 : H2[ob]? = some (BitVec.ofNat 64 (tys.length + 1)) := by simpa using hsb.1
    refine UD.specR_heapLoadI' (C := ctxH C H2) cfgWl (vv cfgSb) ob _ hb0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_assignI cfgWl _ (BitVec.ofNat 64 tys.length) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp; exact ofNat_succ_sub_one tys.length) ?_
    have hlw2 : H2[ob + 1 + tys.length]? = some (Enc.idxW lf) := by
      have := hsb.2 tys.length (by simp)
      rw [List.getElem_append_right (by simp)] at this
      simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H2) cfgLf _ (ob + 1 + tys.length) _ hlw2 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_mulIdx C ob tys.length (by omega)) ?_
    simp only [targetMajorAt, List.getElem?_eq_getElem hcl, pure_bind]
    unfold classLeafAt
    simp only [bind_assoc]
    refine specR_callNIM (C := ctxH C H2) cfgHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cfgLf]
      getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW lf] (by decide) rfl (by decide) hc.cnd.k53.gf
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (fun a w s' st => getAppFn coreWalkFuel lf s2 = .ok (a, s') ∧ Post (ctxH C H2) s2 a w s' st)
      (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec (ctxH C H2) hc.cnd.k53.gf coreWalkFuel lf s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
      (fun hd w s5 st ⟨_, hw, hs, _⟩ => ?_)
    subst hw; subst s5
    refine Knot.specR_tagIteV cfgHd hd 3 (by decide) (by decide) (by simp +decide [Env.get_cons])
      (fun htg => ?_) (fun _ => specR_hangI)
    rw [ite_eq_left_iff.mpr (fun h => absurd (by simp [htg, ETag.const]) h)]
    simp only [bind_assoc]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, cfgParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv cfgHd) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    refine ConPanqueque.T.Big.specR_viewP hd (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
    obtain ⟨I1, us1, rfl⟩ := UD.tagN_const h3
    have hvc : s2.store.viewConst hd = some (I1, us1) := ConPanqueque.T.WC.viewConst_of_view (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
    dsimp only
    refine specR_loadI' cfgNm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW I1) (by decide)
      (by simp [sev, Env.get_cons]) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW I1) [Enc.idxW us1] []) ?_
    by_cases hI : I1 = ms[c].ind
    swap
    · have hne : Enc.idxW I1 ≠ Enc.idxW ms[c].ind := fun e => hI (Enc.idxW_inj e)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hI]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [hI, beq_self_eq_true, pure_bind, ite_true, bind_assoc]
    have hpC2 : C.H <+: H2 := hpC.trans hp2'
    refine specR_callNIH (C := ctxH C H2) cfgR fCnd cndParams [vv cndT, .const 0, vv cndK, vv cndCn, vv cndFv, vv cndFn,
        vv cfgI, vv cfgSb, vv cfgWl, vv cfgLf, vv k53Npc, vv k53Ms, vv k53Us, vv k53Olp, vv k53Ty0, vv k53Pp,
        vv k53Pn, vv k53Pa, vv k53Nd, vv k53Nm] cndBody
      [cellA C ot, BitVec.ofNat 64 0, BitVec.ofNat 64 tbl.length, Enc.idxW cn, cellA C pv, BitVec.ofNat 64 fvs.length,
        BitVec.ofNat 64 i, cellA C ob, BitVec.ofNat 64 tys.length, Enc.idxW lf, BitVec.ofNat 64 ms[c].nPc, cellA C om,
        Enc.idxW ms[c].lvls, cellA C olp, wty, cellA C pp, BitVec.ofNat 64 pfvs.length, cellA C od,
        BitVec.ofNat 64 ms[c].ds.length, wnm] (by decide) rfl (by decide) hc.cnd.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfgParams, ctxEnv],
        trivial⟩
      (Decl.PostU (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cndParams _ rfl hlk)
        (by have h := cnd_spec (σ := σ) mode ra C hok hs hc.cnd p fts hfts hml wty wnm om hM ms[c] olp pp od hlpl hdl (by rw [hpfc]; exact hpl)
              hnpc tbl ot htl cn fvs pv
              hfl i (by omega) H2 hpC2 (eblk_mono hlp (hp.trans hp2')) (by rw [hpfc]; exact blkAt_mono hpf (hp.trans hp2'))
              (blkAt_mono hdb (hp.trans hp2')) (pRep_mono (hp.trans hp2') (fun _ _ => nfRep_mono (hp.trans hp2')) htb)
              (blkAt_mono hfb (hp.trans hp2')) tys lf ob hsb tbl.length 0 H2 s2 (by omega) (by omega) (List.prefix_refl _)
            simp only [List.drop_zero] at h; rw [hpfc] at h; exact h))
      (fun _ w s3 H3 hp3 _ => ?_)
    have hp3' : H2 <+: H3 := hp3
    exact hrec H3 s3 _ _ (hp2'.trans hp3') (fun x hx => by
      simp only [cfgParams, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)

end

end ConPanqueque.T.Ind
