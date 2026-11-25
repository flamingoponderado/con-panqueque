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

end ConPanqueque.T.Ind
