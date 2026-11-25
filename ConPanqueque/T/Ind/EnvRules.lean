import ConPanqueque.T.Ind.EnvRec
import ConPanqueque.T.Ind.RecShapes

/-!
# A recursor's rules in the environment heap

`fwBody`: a firing mode's value-heap record (`FireE` at the value-heap base) turned into its environment words: the
tag and environment copies of the level and parameter lists, returned as a value-heap triple.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- A firing mode's environment words: the tag, the level-list block, the parameter-list block. -/
def FireW (EB : BitVec 64) (EH : List (BitVec 64)) (tg lvw psw : BitVec 64) : IRecRuleFire → Prop
  | .plain => tg = 0
  | .nested lv pins => tg = 1 ∧ ENList EB EH lvw lv ∧ ENList EB EH psw pins
  | .levels lv => tg = 2 ∧ ENList EB EH lvw lv

theorem fireW_mono {EB : BitVec 64} {EH EH' : List (BitVec 64)} (hp : EH <+: EH') {tg lvw psw : BitVec 64}
    {f : IRecRuleFire} (h : FireW EB EH tg lvw psw f) : FireW EB EH' tg lvw psw f := by
  cases f with
  | plain => exact h
  | nested lv pins => exact ⟨h.1, enlist_mono hp h.2.1, enlist_mono hp h.2.2⟩
  | levels lv => exact ⟨h.1, enlist_mono hp h.2⟩

theorem fireE_of_fireW {EB : BitVec 64} {EH : List (BitVec 64)} {q : Nat} {tg lvw psw : BitVec 64}
    {f : IRecRuleFire} (h0 : EH[q]? = some tg) (h1 : EH[q + 1]? = some lvw) (h2 : EH[q + 2]? = some psw)
    (h : FireW EB EH tg lvw psw f) : FireE EB EH q f := by
  cases f with
  | plain => show EH[q]? = some 0; rw [h0, h]
  | nested lv pins => exact ⟨by rw [h0, h.1], ⟨lvw, h1, h.2.1⟩, ⟨psw, h2, h.2.2⟩⟩
  | levels lv => exact ⟨by rw [h0, h.1], ⟨lvw, h1, h.2⟩⟩

theorem blkAt_len_le {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) :
    o + xs.length ≤ H.length := by
  rcases Nat.lt_or_ge 0 xs.length with h0 | h0
  · have := (List.getElem?_eq_some_iff.mp (h.2 (xs.length - 1) (by omega))).1; omega
  · have := (List.getElem?_eq_some_iff.mp h.1).1; omega

def fwF := ofString "fw_f"
def fwT := ofString "fw_t"
def fwLv := ofString "fw_lv"
def fwLn := ofString "fw_ln"
def fwB1 := ofString "fw_b1"
def fwPs := ofString "fw_ps"
def fwPn := ofString "fw_pn"
def fwB2 := ofString "fw_b2"
def fwR := ofString "fw_r"
def fwO := ofString "fw_o"
def fFireEnv := ofString "fireEnvW"

def fwParams : List MlS := [fwF]
def fwLocals : List MlS := [fwT, fwLv, fwLn, fwB1, fwPs, fwPn, fwB2, fwR, fwO]

def fwBody (C : Ctx) : ProgHOL 64 := prologue fwLocals
  (.seq (.assign .local fwT (.load .one (vv fwF)))
  (.ite (.cmp .equal (vv fwT) (.const 0))
    (alloc6 C fwO (.const 0) (.const 0) (.const 0) (.const 0) (.const 0) (.const 0) (.return (vv fwO)))
  (.seq (.assign .local fwLv (.load .one (.op .add [vv fwF, .const 8])))
  (.seq (.assign .local fwLn (.load .one (vv fwLv)))
  (guardP fwLn 58 (envBlkP C fwB1 fwLv fwLn fwR
  (.ite (.cmp .equal (vv fwT) (.const 1))
    (.seq (.assign .local fwPs (.load .one (.op .add [vv fwF, .const 16])))
    (.seq (.assign .local fwPn (.load .one (vv fwPs)))
    (guardP fwPn 58 (envBlkP C fwB2 fwPs fwPn fwR
      (alloc6 C fwO (vv fwT) (vv fwB1) (vv fwB2) (.const 0) (.const 0) (.const 0) (.return (vv fwO)))))))
    (alloc6 C fwO (vv fwT) (vv fwB1) (.const 0) (.const 0) (.const 0) (.const 0) (.return (vv fwO))))))))))

section
variable {σ : Type}

/-- The environment words of `f` in a fresh value-heap triple. -/
def PostFW (C : Ctx) (f : IRecRuleFire) (s : AState) (_ : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  s' = s ∧ ∃ H' EH' o tg lvw psw, C.H <+: H' ∧ C.EH <+: EH' ∧ w = cellA C o ∧ H'[o]? = some tg ∧
    H'[o + 1]? = some lvw ∧ H'[o + 2]? = some psw ∧ FireW C.EB EH' tg lvw psw f ∧ SR (ctxE (ctxH C H') EH') s st

theorem postFW_locals (C : Ctx) (f : IRecRuleFire) (s : AState) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostFW C f s a w s' st → PostFW C f s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, H', EH', o, tg, lvw, psw, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
    ⟨h0, H', EH', o, tg, lvw, psw, h1, h2, h3, h4, h5, h6, h7, sr_of_eq h8 rfl rfl rfl rfl⟩

theorem fw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fwLocals → (ctxEnv C ++ fwParams.zip vals).get x = none :=
  Knot.params_none C fwLocals fwParams vals (by decide) (by decide)

theorem ctxE_H (C : Ctx) (EH : List (BitVec 64)) (H : List (BitVec 64)) : ctxH (ctxE C EH) H = ctxE (ctxH C H) EH := rfl

/-- **A firing mode's environment words.** -/
theorem fw_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (f : IRecRuleFire) (o : Nat) (hf : FireE C.HB C.H o f) (s : AState) :
    SpecR (σ := σ) (Pre C s (fwParams.zip [cellA C o])) (fwBody C) s (pure ()) (PostFW C f s) := by
  refine specR_prologue (postFW_locals _ _ _) (fw_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : C.H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  cases f with
  | plain =>
    refine UD.specR_heapLoadI' (C := C) fwT _ o _ hf (by decide) (by simp +decide [Env.get, fwParams, ctxEnv]) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_alloc6I hok fwO _ _ _ _ _ _ 0 0 0 0 0 0 (by decide) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun H2 ws hp2 hws hroom => ?_)
    obtain ⟨g0, g1, g2, -⟩ := img6_get H2 ws 0 0 0 0 0 0 hws
    exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨rfl, _, C.EH, H2.length, 0, 0, 0, hp2.trans (img6_prefix H2 ws _ _ _ _ _ _ hws), List.prefix_refl _,
        rfl, g0, g1, g2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | nested lv pins =>
    obtain ⟨h0, ⟨w1, hw1, ol, hwlo, hebl⟩, ⟨w2, hw2, op, hwpo, hebp⟩⟩ := hf
    have hbl : BlkAt C.H ol (lv.map Enc.idxW) := hebl
    have hbp : BlkAt C.H op (pins.map Enc.idxW) := hebp
    refine UD.specR_heapLoadI' (C := C) fwT _ o _ h0 (by decide) (by simp +decide [Env.get, fwParams, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := C) fwLv _ (o + 1) _ hw1 (by decide)
      (by simp +decide [sev, Env.get, fwParams, ctxEnv]; exact cellA_add8 C o) ?_
    refine UD.specR_heapLoadI' (C := C) fwLn _ ol _ hbl.1 (by decide) (by simp +decide [Env.get, hwlo]; rfl) ?_
    have hbll := blkAt_len_le hbl
    refine specR_guardI fwLn (lv.map Enc.idxW).length 58 (by decide) (by simp [Env.get]) (by omega) (fun hl58 => ?_)
    refine specR_envBlkI hok hcp fwB1 fwLv fwLn fwR ol _ hbl (by omega) (by decide) (by decide)
      (by decide) (by decide) (by simp +decide [Env.get, hwlo]; rfl) (by simp +decide [Env.get])
      (fun EH1 r1 hp1 heb1 => ?_)
    have hok1 := ctxOK_E hok hp1
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := ctxE C EH1) fwPs _ (o + 2) _ hw2 (by decide)
      (by simp +decide [sev, Env.get, fwParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
    refine UD.specR_heapLoadI' (C := ctxE C EH1) fwPn _ op _ hbp.1 (by decide) (by simp +decide [Env.get, hwpo]; rfl) ?_
    have hbpl := blkAt_len_le hbp
    refine specR_guardI fwPn (pins.map Enc.idxW).length 58 (by decide) (by simp [Env.get]) (by omega) (fun hp58 => ?_)
    refine specR_envBlkI hok1 hcp fwB2 fwPs fwPn fwR op _ hbp (by omega) (by decide) (by decide)
      (by decide) (by decide) (by simp +decide [Env.get, hwpo]; rfl) (by simp +decide [Env.get])
      (fun EH2 r2 hp2 heb2 => ?_)
    have hok2 := ctxOK_E hok1 hp2
    refine specR_alloc6I hok2 fwO _ _ _ _ _ _ 1 (ecell C C.EH.length) (ecell C EH1.length) 0 0 0 (by decide)
      (fun _ => by simp +decide [Env.get]) (fun _ => by simp +decide [Env.get]) (fun _ => by simp +decide [Env.get]; rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun H2 ws hp3 hws hroom => ?_)
    obtain ⟨g0, g1, g2, -⟩ := img6_get H2 ws 1 (ecell C C.EH.length) (ecell C EH1.length) 0 0 0 hws
    exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨rfl, _, EH2, H2.length, 1, ecell C C.EH.length, ecell C EH1.length,
        hp3.trans (img6_prefix H2 ws _ _ _ _ _ _ hws), hp1.trans hp2, rfl, g0, g1, g2,
        ⟨rfl, ⟨C.EH.length, rfl, eblk_mono heb1 hp2⟩, ⟨EH1.length, rfl, heb2⟩⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | levels lv =>
    obtain ⟨h0, ⟨w1, hw1, ol, hwlo, hebl⟩⟩ := hf
    have hbl : BlkAt C.H ol (lv.map Enc.idxW) := hebl
    refine UD.specR_heapLoadI' (C := C) fwT _ o _ h0 (by decide) (by simp +decide [Env.get, fwParams, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := C) fwLv _ (o + 1) _ hw1 (by decide)
      (by simp +decide [sev, Env.get, fwParams, ctxEnv]; exact cellA_add8 C o) ?_
    refine UD.specR_heapLoadI' (C := C) fwLn _ ol _ hbl.1 (by decide) (by simp +decide [Env.get, hwlo]; rfl) ?_
    have hbll := blkAt_len_le hbl
    refine specR_guardI fwLn (lv.map Enc.idxW).length 58 (by decide) (by simp [Env.get]) (by omega) (fun hl58 => ?_)
    refine specR_envBlkI hok hcp fwB1 fwLv fwLn fwR ol _ hbl (by omega) (by decide) (by decide)
      (by decide) (by decide) (by simp +decide [Env.get, hwlo]; rfl) (by simp +decide [Env.get])
      (fun EH1 r1 hp1 heb1 => ?_)
    have hok1 := ctxOK_E hok hp1
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_alloc6I hok1 fwO _ _ _ _ _ _ 2 (ecell C C.EH.length) 0 0 0 0 (by decide)
      (fun _ => by simp +decide [Env.get]) (fun _ => by simp +decide [Env.get] <;> rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun H2 ws hp3 hws hroom => ?_)
    obtain ⟨g0, g1, g2, -⟩ := img6_get H2 ws 2 (ecell C C.EH.length) 0 0 0 0 hws
    exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨rfl, _, EH1, H2.length, 2, ecell C C.EH.length, 0,
        hp3.trans (img6_prefix H2 ws _ _ _ _ _ _ hws), hp1, rfl, g0, g1, g2,
        ⟨rfl, ⟨C.EH.length, rfl, heb1⟩⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def rwRs := ofString "rw_rs"
def rwD := ofString "rw_d"
def rwI := ofString "rw_i"
def rwN := ofString "rw_n"
def rwTg := ofString "rw_tg"
def rwLv := ofString "rw_lv"
def rwPs := ofString "rw_ps"
def rwQ := ofString "rw_q"
def rwCt := ofString "rw_ct"
def rwNf := ofString "rw_nf"
def rwRh := ofString "rw_rh"
def rwX := ofString "rw_x"
def rwR := ofString "rw_r"
def fRuleFill := ofString "ruleEnvFill"

def rwParams : List MlS := [rwRs, rwD, rwI, rwN, rwTg, rwLv, rwPs]
def rwLocals : List MlS := [rwQ, rwCt, rwNf, rwRh, rwX, rwR]

/-- The rules (value-heap pointer block at `rwRs`, from `rwI`) as environment records at the firing words, their
pointers into the value-heap block at `rwD`. -/
def rwBody (C : Ctx) : ProgHOL 64 := prologue rwLocals
  (.ite (.cmp .lower (vv rwI) (vv rwN))
    (.seq (.assign .local rwQ (.load .one (.op .add [vv rwRs, .op .add [.panop .mul [vv rwI, .const 8], .const 8]])))
    (.seq (.assign .local rwCt (.load .one (vv rwQ)))
    (.seq (.assign .local rwNf (.load .one (.op .add [vv rwQ, .const 8])))
    (.seq (.assign .local rwRh (.load .one (.op .add [vv rwQ, .const 40])))
    (envRecP C rwX [vv rwCt, vv rwNf, vv rwTg, vv rwLv, vv rwPs, vv rwRh]
    (.seq (.store (.op .add [vv rwD, .op .add [.panop .mul [vv rwI, .const 8], .const 8]]) (vv rwX))
    (.seq (.call (some (some (.local, rwR), none)) fRuleFill
      [vv rwRs, vv rwD, .op .add [vv rwI, .const 1], vv rwN, vv rwTg, vv rwLv, vv rwPs])
      (.return (.const 0)))))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- A value-heap block of rule pointers at the value-heap base. -/
def VRulesAt (C : Ctx) (H : List (BitVec 64)) (ob : Nat) (rules : List IRecRule) : Prop :=
  H[ob]? = some (BitVec.ofNat 64 rules.length) ∧
    ∀ i (hi : i < rules.length), ∃ q, H[ob + 1 + i]? = some (cellA C q) ∧ RuleE C.HB H q rules[i]

/-- The rules from position `i` on, past the frozen value-heap prefix `Hc` and the environment heap `EH`. -/
def PostRW (C : Ctx) (Hc EH : List (BitVec 64)) (od : Nat) (rules : List IRecRule) (f : IRecRuleFire) (i : Nat)
    (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' EH', Hc <+: H' ∧ EH <+: EH' ∧ SR (ctxE (ctxH C H') EH') s' st ∧
    ∀ j (hj : j < rules.length), i ≤ j → ∃ q, H'[od + 1 + j]? = some (ecell C q) ∧
      RuleE C.EB EH' q { rules[j] with fire := f }

theorem postRW_locals (C : Ctx) (Hc EH : List (BitVec 64)) (od : Nat) (rules : List IRecRule) (f : IRecRuleFire)
    (i : Nat) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRW C Hc EH od rules f i a w s' st → PostRW C Hc EH od rules f i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', EH', h1, h2, h3, h4⟩ => ⟨H', EH', h1, h2, sr_of_eq h3 rfl rfl rfl rfl, h4⟩

theorem rw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rwLocals → (ctxEnv C ++ rwParams.zip vals).get x = none :=
  Knot.params_none C rwLocals rwParams vals (by decide) (by decide)

theorem ruleE_mono' {EB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') {q : Nat} {r : IRecRule}
    (h : RuleE EB H q r) : RuleE EB H' q r :=
  ⟨get_prefix h.1 hp, ⟨get_prefix h.2.1.1 hp, h.2.1.2⟩, fireE_mono hp h.2.2.1, get_prefix h.2.2.2 hp⟩

/-- **The rules' environment records** from position `i`. -/
theorem rw_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fRuleFill = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one))
    (rules : List IRecRule) (ob od : Nat) (H0 : List (BitVec 64)) (hrs : VRulesAt C H0 ob rules)
    (f : IRecRuleFire) (tg lvw psw : BitVec 64) :
    ∀ k i (H Hc EH : List (BitVec 64)) (s : AState), rules.length - i = k → i ≤ rules.length → H0 <+: Hc →
      Hc.length ≤ od + 1 + i → Hc <+: H → od + 1 + rules.length ≤ H.length → C.EH <+: EH →
      FireW C.EB EH tg lvw psw f →
      SpecR (Pre (σ := σ) (ctxE (ctxH C H) EH) s (rwParams.zip [cellA C ob, cellA C od, BitVec.ofNat 64 i,
        BitVec.ofNat 64 rules.length, tg, lvw, psw])) (rwBody C) s (pure ()) (PostRW C Hc EH od rules f i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe hfw
    refine specR_prologue (postRW_locals _ _ _ _ _ _ _) (rw_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, rwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, EH, hp, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe hfw
    have hil : i < rules.length := by omega
    refine specR_prologue (postRW_locals _ _ _ _ _ _ _) (rw_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i rules.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨q, hq, hre⟩ := hrs.2 i hil
    have hre' := ruleE_mono' h0H hre
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) rwQ _ (ob + 1 + i) _ (get_prefix hq h0H) (by decide)
      (by simp +decide [sev, Env.get, rwParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) rwCt _ q _ hre'.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) rwNf _ (q + 1) _ hre'.2.1.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C q) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) rwRh _ (q + 5) _ hre'.2.2.2 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_plus C q 5) ?_
    have hokE : CtxOK (ctxE (ctxH C H) EH) := ctxOK_E (ctxOK_H hok H) hpe
    refine specR_envRecI hokE rwX [vv rwCt, vv rwNf, vv rwTg, vv rwLv, vv rwPs, vv rwRh]
      [Enc.idxW rules[i].ctor, BitVec.ofNat 64 rules[i].nfields, tg, lvw, psw, Enc.idxW rules[i].rhs]
      (by decide) rfl (by decide)
      (fun w j hj hj' => by
        rcases j with _ | _ | _ | _ | _ | _ | j <;>
          first | (simp +decide [sev, Env.get, rwParams, ctxEnv]; done) | (simp at hj; omega))
      (fun EH1 hp1 hl1 hv1 => ?_)
    have hq0 : ∀ j (hj : j < 6), EH1[EH.length + j]? = some ([Enc.idxW rules[i].ctor, BitVec.ofNat 64 rules[i].nfields,
        tg, lvw, psw, Enc.idxW rules[i].rhs] : List (BitVec 64))[j] := fun j hj => hv1 j (by simpa using hj)
    have hrE : RuleE C.EB EH1 EH.length { rules[i] with fire := f } :=
      ⟨hq0 0 (by decide), ⟨hq0 1 (by decide), hre'.2.1.2⟩,
        fireE_of_fireW (hq0 2 (by decide)) (hq0 3 (by decide)) (hq0 4 (by decide)) (fireW_mono hp1 hfw),
        hq0 5 (by decide)⟩
    have hj : od + 1 + i < (ctxH (ctxE (ctxH C H) EH1) H).H.length := by show od + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok H) (hpe.trans hp1)) _ (vv rwX) (od + 1 + i) hj (ecell C EH.length)
      (by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv]; exact cellA_mulIdx C od i (by omega))
      (by simp [sev, Env.get_cons]; rfl) ?_
    change SpecR (Inv (ctxE (ctxH C (H.set (od + 1 + i) (ecell C EH.length))) EH1) _ _ _ _) _ _ _ _
    generalize hB : H.set (od + 1 + i) (ecell C EH.length) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[od + 1 + i]? = some (ecell C EH.length) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hp
    let Hc' := B.take (od + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C B) EH1) rwR fRuleFill rwParams
      [vv rwRs, vv rwD, .op .add [vv rwI, .const 1], vv rwN, vv rwTg, vv rwLv, vv rwPs] (rwBody C)
      [cellA C ob, cellA C od, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rules.length, tg, lvw, psw]
      (by decide) rfl (by decide) hcode ?_
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostRW C Hc' EH1 od rules f (i + 1) a w s' st)
      (fun a w s' C' => s' = s ∧ ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc' <+: H' ∧ EH1 <+: EH' ∧
        ∀ j (hj : j < rules.length), i + 1 ≤ j → ∃ q, H'[od + 1 + j]? = some (ecell C q) ∧
          RuleE C.EB EH' q { rules[j] with fire := f })
      (fun a w s' st ⟨hr, H', EH', hp', hpe', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨_, ⟨rfl, H', EH', rfl, hp', hpe', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' EH1 s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega)
          (hpe.trans hp1) (fireW_mono hp1 hfw) _ (pre_of_lookups hu rwParams _ rfl hlk)))
      (fun a w s' C' ⟨hs', H', EH', eC, hp', hpe', hc'⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, rwParams, ctxEnv], trivial⟩
    subst eC hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', EH', hHcc.trans hp', hp1.trans hpe', sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by
        rcases Nat.lt_or_ge i j with h | h
        · exact hc' j hj (by omega)
        · have e : j = i := by omega
          subst e
          refine ⟨EH.length, ?_, ruleE_mono' hpe' hrE⟩
          exact get_prefix (show Hc'[od + 1 + j]? = some (ecell C EH.length) by
            simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'⟩)

end

def rqR := ofString "rq_r"
def rqF := ofString "rq_f"
def rqCv := ofString "rq_cv"
def rqRp := ofString "rq_rp"
def rqMi := ofString "rq_mi"
def rqRw := ofString "rq_rw"
def rqIk := ofString "rq_ik"
def rqT3 := ofString "rq_t3"
def rqTg := ofString "rq_tg"
def rqLv := ofString "rq_lv"
def rqPs := ofString "rq_ps"
def rqRn := ofString "rq_rn"
def rqD := ofString "rq_d"
def rqX := ofString "rq_x"
def rqB := ofString "rq_b"
def rqO := ofString "rq_o"
def fRecRec := ofString "recRecW"

def rqParams : List MlS := [rqR, rqF]
def rqLocals : List MlS := [rqCv, rqRp, rqMi, rqRw, rqIk, rqT3, rqTg, rqLv, rqPs, rqRn, rqD, rqX, rqB, rqO]

/-- A recursor's environment record (`RecShape` at `rqR`, its firing mode's value record at `rqF`). -/
def rqBody (C : Ctx) : ProgHOL 64 := prologue rqLocals
  (.seq (.assign .local rqCv (.load .one (vv rqR)))
  (.seq (.assign .local rqRp (.load .one (.op .add [vv rqR, .const 8])))
  (.seq (.assign .local rqMi (.load .one (.op .add [vv rqR, .const 16])))
  (.seq (.assign .local rqRw (.load .one (.op .add [vv rqR, .const 32])))
  (.seq (.assign .local rqIk (.load .one (.op .add [vv rqR, .const 40])))
  (.seq (.call (some (some (.local, rqT3), none)) fFireEnv [vv rqF])
  (.seq (.assign .local rqTg (.load .one (vv rqT3)))
  (.seq (.assign .local rqLv (.load .one (.op .add [vv rqT3, .const 8])))
  (.seq (.assign .local rqPs (.load .one (.op .add [vv rqT3, .const 16])))
  (.seq (.assign .local rqRn (.load .one (vv rqRw)))
  (guardP rqRn 58
  (allocP C rqD (.shift .lsl (.op .add [vv rqRn, .const 1]) (.const 3))
  (.seq (.store (vv rqD) (vv rqRn))
  (.seq (.call (some (some (.local, rqX), none)) fRuleFill [vv rqRw, vv rqD, .const 0, vv rqRn, vv rqTg, vv rqLv, vv rqPs])
  (envBlkP C rqB rqD rqRn rqX
  (.seq (.call (some (some (.local, rqO), none)) fConstRec
    [vv rqCv, .const 5, vv rqMi, vv rqRp, vv rqIk, vv rqB, .const 0, .const 0])
    (.return (vv rqO))))))))))))))))))

section
variable {σ : Type}

/-- A fresh recursor record, past the value heap and the environment heap. -/
def PostRQ (C : Ctx) (ci : IConstantInfo) (s : AState) (_ : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  s' = s ∧ ∃ H' EH o, C.H <+: H' ∧ C.EH <+: EH ∧ C.EH.length ≤ o ∧ w = ecell C o ∧ CIE C.EB EH o ci ∧
    SR (ctxE (ctxH C H') EH) s st

theorem postRQ_locals (C : Ctx) (ci : IConstantInfo) (s : AState) : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostRQ C ci s a w s' st → PostRQ C ci s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h0, H', EH, o, h1, h2, h3, h4, h5, h6⟩ => ⟨h0, H', EH, o, h1, h2, h3, h4, h5, sr_of_eq h6 rfl rfl rfl rfl⟩

theorem rq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rqLocals → (ctxEnv C ++ rqParams.zip vals).get x = none :=
  Knot.params_none C rqLocals rqParams vals (by decide) (by decide)

theorem pure_run_unit (s s' : AState) (a : Unit) (h : (pure () : AM Unit) s = .ok (a, s')) : s' = s := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- **A recursor's record**, its rules firing as `f`. -/
theorem rq_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcf : C.code.lookup fFireEnv = some (fwParams.map (fun p => (p, ShapeHOL.one)), fwBody C, .one))
    (hcr : C.code.lookup fRuleFill = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one))
    (hcw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one))
    (rc : RecShape) (orc : Nat) (hrr : RecRep C C.H orc rc) (hlps : rc.cvR.levelParams.length < 2 ^ 60)
    (f : IRecRuleFire) (ofi : Nat) (hf : FireE C.HB C.H ofi f) (s : AState) :
    SpecR (σ := σ) (Pre C s (rqParams.zip [cellA C orc, cellA C ofi])) (rqBody C) s (pure ())
      (PostRQ C (.recInfo rc.cvR rc.mI rc.rP rc.isK (rc.rules.map ({ · with fire := f }))) s) := by
  refine specR_prologue (postRQ_locals _ _ _) (rq_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : C.H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  obtain ⟨⟨ocv, hocv, hcv⟩, ⟨hrp, hrpb⟩, ⟨hmi, hmib⟩, -, ⟨w, hw, ob, hwob, hrl0, hrls⟩, hik⟩ := hrr
  refine UD.specR_heapLoadI' (C := C) rqCv _ orc _ hocv (by decide) (by simp +decide [Env.get, rqParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) rqRp _ (orc + 1) _ hrp (by decide)
    (by simp +decide [sev, Env.get, rqParams, ctxEnv]; exact cellA_add8 C orc) ?_
  refine UD.specR_heapLoadI' (C := C) rqMi _ (orc + 2) _ hmi (by decide)
    (by simp +decide [sev, Env.get, rqParams, ctxEnv]; exact cellA_add_ofNat C orc 2) ?_
  refine UD.specR_heapLoadI' (C := C) rqRw _ (orc + 4) _ hw (by decide)
    (by simp +decide [sev, Env.get, rqParams, ctxEnv]; exact cellA_add_ofNat C orc 4) ?_
  refine UD.specR_heapLoadI' (C := C) rqIk _ (orc + 5) _ hik (by decide)
    (by simp +decide [sev, Env.get, rqParams, ctxEnv]; exact cellA_add_ofNat C orc 5) ?_
  -- the firing mode's environment words
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
  refine specR_callNC (C := C) rqT3 fFireEnv fwParams [vv rqF] (fwBody C) [cellA C ofi] (by decide) rfl (by decide) hcf
    ⟨by simp +decide [sev, Env.get_cons, Env.get, rqParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostFW C f s a w s' st)
    (fun a w s' C' => s' = s ∧ ∃ H1 EH1 o3 tg lvw psw, C' = ctxE (ctxH C H1) EH1 ∧ C.H <+: H1 ∧ C.EH <+: EH1 ∧
      w = cellA C o3 ∧ H1[o3]? = some tg ∧ H1[o3 + 1]? = some lvw ∧ H1[o3 + 2]? = some psw ∧
      FireW C.EB EH1 tg lvw psw f)
    (fun a w s' st ⟨hr, h0, H1, EH1, o3, tg, lvw, psw, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
      ⟨_, ⟨(pure_run_unit _ _ _ hr), H1, EH1, o3, tg, lvw, psw, rfl, h1, h2, h3, h4, h5, h6, h7⟩,
        by rw [pure_run_unit _ _ _ hr]; exact h8⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact fw_spec C hok hcp f ofi hf s _ (pre_of_lookups hu fwParams _ rfl hlk)))
    (fun _ w3 s1 C1 ⟨hs1, H1, EH1, o3, tg, lvw, psw, eC1, hp1, hpe1, hw3, ht0, ht1, ht2, hfw⟩ => ?_)
  subst eC1 hw3; subst s1
  have hok1 : CtxOK (ctxE (ctxH C H1) EH1) := ctxOK_E (ctxOK_H hok H1) hpe1
  refine UD.specR_heapLoadI' (C := ctxE (ctxH C H1) EH1) rqTg _ o3 _ ht0 (by decide) (by simp +decide [Env.get] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxE (ctxH C H1) EH1) rqLv _ (o3 + 1) _ ht1 (by decide)
    (by simp +decide [sev, Env.get]; exact cellA_add8 C o3) ?_
  refine UD.specR_heapLoadI' (C := ctxE (ctxH C H1) EH1) rqPs _ (o3 + 2) _ ht2 (by decide)
    (by simp +decide [sev, Env.get]; exact cellA_add_ofNat C o3 2) ?_
  have hrl0' := get_prefix hrl0 hp1
  refine UD.specR_heapLoadI' (C := ctxE (ctxH C H1) EH1) rqRn _ ob _ hrl0' (by decide)
    (by simp +decide [Env.get, hwob]; rfl) ?_
  have hrsl : ob + rc.rules.length ≤ C.H.length := by
    rcases Nat.lt_or_ge 0 rc.rules.length with h | h
    · obtain ⟨q, hq, -⟩ := hrls (rc.rules.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hq).1; omega
    · have := (List.getElem?_eq_some_iff.mp hrl0).1; omega
  refine specR_guardI rqRn rc.rules.length 58 (by decide) (by simp [Env.get]) (by omega) (fun hn58 => ?_)
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
  have hHN1' : H1.length ≤ C.HN := hHN1
  -- the value-heap block of rule pointers
  refine specR_allocI (C := ctxE (ctxH C H1) EH1) rqD _ (rc.rules.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H1 <+: H2 := hp2
  change SpecR (Inv (ctxE (ctxH C (H2 ++ ws)) EH1) _ _ _ _) _ _ _ _
  have hq0 : H2.length < (ctxE (ctxH C (H2 ++ ws)) EH1).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_E (ctxOK_H hok (H2 ++ ws)) hpe1) (vv rqD) (vv rqRn) H2.length hq0
    (BitVec.ofNat 64 rc.rules.length) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  change SpecR (Inv (ctxE (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 rc.rules.length))) EH1) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 rc.rules.length) = B
  have hBlen : B.length = H2.length + (rc.rules.length + 1) := by rw [← hB]; simp [hws]
  have hB0 : B[H2.length]? = some (BitVec.ofNat 64 rc.rules.length) := by
    rw [← hB, List.getElem?_set_self (by simp; omega)]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hpB
  have hHc0 : Hc[H2.length]? = some (BitVec.ofNat 64 rc.rules.length) := by
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega)]; exact hB0
  have hvr : VRulesAt C C.H ob rc.rules := ⟨hrl0, fun i hi => hrls i hi⟩
  -- the rules
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
  refine specR_callNC (C := ctxE (ctxH C B) EH1) rqX fRuleFill rwParams
    [vv rqRw, vv rqD, .const 0, vv rqRn, vv rqTg, vv rqLv, vv rqPs] (rwBody C)
    [cellA C ob, cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 rc.rules.length, tg, lvw, psw]
    (by decide) rfl (by decide) hcr
    ⟨by simp +decide [sev, Env.get, hwob]; rfl, by simp +decide [sev, Env.get] <;> rfl, rfl,
      by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], by simp +decide [sev, Env.get],
      by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostRW C Hc EH1 H2.length rc.rules f 0 a w s' st)
    (fun a w s' C' => s' = s ∧ ∃ H3 EH2, C' = ctxE (ctxH C H3) EH2 ∧ Hc <+: H3 ∧ EH1 <+: EH2 ∧
      ∀ j (hj : j < rc.rules.length), 0 ≤ j → ∃ q, H3[H2.length + 1 + j]? = some (ecell C q) ∧
        RuleE C.EB EH2 q { rc.rules[j] with fire := f })
    (fun a w s' st ⟨hr, H3, EH2, h1, h2, h3, h4⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, H3, EH2, rfl, h1, h2, h4⟩, h3⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact rw_spec C hok hcr rc.rules ob H2.length C.H hvr f tg lvw psw _ 0 B Hc EH1 s rfl (Nat.zero_le _)
        ((hp1.trans hp2').trans hpc) (by simp [Hc]) (List.take_prefix _ _) (by omega) hpe1 hfw _
        (pre_of_lookups hu rwParams _ rfl hlk)))
    (fun _ w4 s2 C2 ⟨hs2, H3, EH2, eC2, hp3, hpe2, hrs3⟩ => ?_)
  subst eC2; subst s2
  -- the pointer block, copied
  let xs : List (BitVec 64) := (List.range rc.rules.length).map (fun j => (H3[H2.length + 1 + j]?).getD 0)
  have hxsl : xs.length = rc.rules.length := by simp [xs]
  have hxs : ∀ j (hj : j < xs.length), ∃ q, xs[j] = ecell C q ∧ RuleE C.EB EH2 q { rc.rules[j]'(by omega) with fire := f } := by
    intro j hj
    obtain ⟨q, hq, hre⟩ := hrs3 j (by omega) (Nat.zero_le _)
    exact ⟨q, by simp [xs, hq], hre⟩
  have hbx : BlkAt H3 H2.length xs := by
    refine ⟨by rw [hxsl]; exact get_prefix hHc0 hp3, fun j hj => ?_⟩
    obtain ⟨q, hq, -⟩ := hrs3 j (by omega) (Nat.zero_le _)
    simp [xs, hq]
  have hok3 : CtxOK (ctxE (ctxH C H3) EH2) := ctxOK_E (ctxOK_H hok H3) (hpe1.trans hpe2)
  refine specR_envBlkI hok3 hcp rqB rqD rqRn rqX H2.length xs hbx (by omega) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, hxsl])
    (fun EH3 w5 hpe3 hebx => ?_)
  -- the constant record
  have hok4 : CtxOK (ctxE (ctxH C H3) EH3) := ctxOK_E (ctxOK_H hok H3) ((hpe1.trans hpe2).trans hpe3)
  have hpH3 : C.H <+: H3 := ((hp1.trans hp2').trans hpc).trans hp3
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
  refine specR_callNC (C := ctxE (ctxH C H3) EH3) rqO fConstRec cwParams
    [vv rqCv, .const 5, vv rqMi, vv rqRp, vv rqIk, vv rqB, .const 0, .const 0] (cwBody C)
    [cellA C ocv, 5, BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, boolW rc.isK, ecell C EH2.length, 0, 0]
    (by decide) rfl (by decide) hcw
    ⟨by simp +decide [sev, Env.get], rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get],
      by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, rfl, rfl, trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧
      PostCW (ctxE (ctxH C H3) EH3) rc.cvR 5 [BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, boolW rc.isK,
        ecell C EH2.length, 0, 0] s a w s' st)
    (fun a w s' C' => s' = s ∧ ∃ EH4 o, C' = ctxE (ctxH C H3) EH4 ∧ EH3 <+: EH4 ∧ EH3.length ≤ o ∧ w = ecell C o ∧
      CVE C.EB EH4 (o + 1) rc.cvR ∧ EH4[o]? = some 5 ∧
      (∀ j (hj : j < 6), EH4[o + 4 + j]? = some ([BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, boolW rc.isK,
        ecell C EH2.length, 0, 0] : List (BitVec 64))[j]))
    (fun a w s' st ⟨hr, h0, EH4, o, h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, EH4, o, rfl, h1, h2, h3, h4, h5, fun j hj => h6 j (by simpa using hj)⟩,
        by rw [pure_run_unit _ _ _ hr]; exact h7⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact cw_spec (ctxE (ctxH C H3) EH3) hok4 hcp rc.cvR ocv (cvRep_mono hpH3 hcv) hlps 5 _ _ _ _ _ _ s _
        (pre_of_lookups hu cwParams _ rfl hlk)))
    (fun _ w6 s3 C3 ⟨hs3, EH4, o, eC3, hpe4, hol, hw6, hcve, htg, hfs⟩ => ?_)
  subst eC3 hw6; subst s3
  have hpeA : C.EH <+: EH4 := ((hpe1.trans hpe2).trans hpe3).trans hpe4
  have hl1 := hpe1.length_le
  have hl2 := hpe2.length_le
  have hl3 := hpe3.length_le
  have hol' : EH3.length ≤ o := hol
  have hl1' : C.EH.length ≤ EH1.length := hl1
  have hl2' : EH1.length ≤ EH2.length := hl2
  have hl3' : EH2.length ≤ EH3.length := hl3
  exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, H3, EH4, o, hpH3, hpeA, by omega, rfl,
      ⟨hcve, htg, ⟨by simpa using hfs 0 (by decide), hmib⟩, ⟨by simpa using hfs 1 (by decide), hrpb⟩,
        by simpa using hfs 2 (by decide),
        ⟨ecell C EH2.length, by simpa using hfs 3 (by decide), EH2.length, rfl,
          by
            have h0 : EH4[EH2.length]? = some (BitVec.ofNat 64 xs.length) := (eblk_mono hebx hpe4).1
            simpa [hxsl] using h0,
          fun i hi => by
            simp only [List.length_map] at hi
            obtain ⟨q, hq, hre⟩ := hxs i (by omega)
            refine ⟨q, ?_, ?_⟩
            · have this : EH4[EH2.length + 1 + i]? = some xs[i] := (eblk_mono hebx hpe4).2 i (by omega)
              rw [this, hq]; rfl
            · simp only [List.getElem_map]
              exact ruleE_mono' (hpe3.trans hpe4) hre⟩⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
