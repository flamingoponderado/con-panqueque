import ConPanqueque.T.Decl.NameNodup
import ConPanqueque.T.Core.NzParam
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Level parameters, defined: the level side

The declaration's level-parameter names are a heap block of name handles. `lpm` asks whether a name is among them
(structural name equality); `lpd` walks a level tree, every parameter defined; `lpa` runs `lpd` over a universe
list.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def lmN := ofString "lm_n"
def lmP := ofString "lm_p"
def lmJ := ofString "lm_j"
def lmL := ofString "lm_l"
def lmK := ofString "lm_k"
def lmE := ofString "lm_e"
def lmR := ofString "lm_r"
def fLpm := ofString "lpNameMem"

def lmParams : List MlS := [lmN, lmP, lmJ, lmL]
def lmLocals : List MlS := [lmK, lmE, lmR]

/-- Is name `lmN` among the block's names from index `lmJ` on (block at `lmP`, `lmL` names). -/
def lmBody : ProgHOL 64 := prologue lmLocals
  (.ite (.cmp .lower (vv lmJ) (vv lmL))
    (.seq (.assign .local lmK (.load .one (.op .add [vv lmP, .op .add [.panop .mul [vv lmJ, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, lmE), none)) NEq.fNeq [vv lmK, vv lmN])
    (.ite (vv lmE) (.return (.const 1))
      (.seq (.call (some (some (.local, lmR), none)) fLpm [vv lmN, vv lmP, .op .add [vv lmJ, .const 1], vv lmL])
        (.return (vv lmR))))))
    (.return (.const 0)))

def ldU := ofString "ld_u"
def ldP := ofString "ld_p"
def ldL := ofString "ld_l"
def ldA := ofString "ld_a"
def ldB := ofString "ld_b"
def ldR := ofString "ld_r"
def fLpd := ofString "lpDefined"

def ldParams : List MlS := [ldU, ldP, ldL]
def ldLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ldA, ldB, ldR]

/-- Every parameter of level `ldU` is among the block's names. -/
def ldBody : ProgHOL 64 := prologue ldLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv ldU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 1))
  (.seq (.assign .local ldA (.load .one (vv lRp)))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.call (some (some (.local, ldR), none)) fLpm [vv ldA, vv ldP, .const 0, vv ldL]) (.return (vv ldR)))
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.call (some (some (.local, ldR), none)) fLpd [vv ldA, vv ldP, vv ldL]) (.return (vv ldR)))
  (.seq (.assign .local ldB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, ldR), none)) fLpd [vv ldA, vv ldP, vv ldL])
  (.ite (vv ldR)
    (.seq (.call (some (some (.local, ldR), none)) fLpd [vv ldB, vv ldP, vv ldL]) (.return (vv ldR)))
    (.return (.const 0))))))))))))

def laU := ofString "la_u"
def laP := ofString "la_p"
def laL := ofString "la_l"
def laI := ofString "la_i"
def laA := ofString "la_a"
def laR := ofString "la_r"
def fLpa := ofString "lpDefinedAll"

def laParams : List MlS := [laU, laP, laL, laI]
def laLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, laA, laR]

/-- Every level of universe list `laU` from position `laI` on passes `lpd`. -/
def laBody : ProgHOL 64 := prologue laLocals
  (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv laU)) (.seq lsViewP
  (.ite (.cmp .lower (vv laI) (vv lRn))
    (.seq (.assign .local laA (.load .one (.op .add [vv lRp, .shift .lsl (vv laI) (.const 3)])))
    (.seq (.call (some (some (.local, laR), none)) fLpd [vv laA, vv laP, vv laL])
    (.ite (vv laR)
      (.seq (.call (some (some (.local, laR), none)) fLpa [vv laU, vv laP, vv laL, .op .add [vv laI, .const 1]])
        (.return (vv laR)))
      (.return (.const 0)))))
    (.return (.const 1))))))

structure LpCodes (C : Ctx) : Prop where
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  lpm : C.code.lookup fLpm = some (lmParams.map (fun p => (p, ShapeHOL.one)), lmBody, .one)
  lpd : C.code.lookup fLpd = some (ldParams.map (fun p => (p, ShapeHOL.one)), ldBody, .one)
  lpa : C.code.lookup fLpa = some (laParams.map (fun p => (p, ShapeHOL.one)), laBody, .one)

/-- The parameter names: a heap block of handles reading back to `ks`. -/
structure LpsAt (C : Ctx) (s : AState) (o : Nat) (xs : List NIdx) (ks : List ConLeche.Name) : Prop where
  blk : BlkAt C.H o (xs.map Enc.idxW)
  len : ks.length = xs.length
  den : ∀ j (hj : j < xs.length), denoteN s.store.ns xs[j] = some (ks[j]'(by rw [len]; exact hj))
  small : xs.length < 2 ^ 62

section
variable {σ : Type}

theorem lm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lmLocals → (ctxEnv C ++ lmParams.zip vals).get x = none :=
  Knot.params_none C lmLocals lmParams vals (by decide) (by decide)

theorem ld_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ldLocals → (ctxEnv C ++ ldParams.zip vals).get x = none :=
  Knot.params_none C ldLocals ldParams vals (by decide) (by decide)

theorem la_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ laLocals → (ctxEnv C ++ laParams.zip vals).get x = none :=
  Knot.params_none C laLocals laParams vals (by decide) (by decide)

/-- **`lpm`**: the name is among the parameters from index `j` on. -/
theorem lpm_spec (C : Ctx) (hc : LpCodes C) (s : AState) {o : Nat} {xs : List NIdx} {ks : List ConLeche.Name}
    (hL : LpsAt C s o xs ks) (n : NIdx) (nm : ConLeche.Name) (fn : Nat) (hn : denoteNAux s.store.ns fn n = some nm) :
    ∀ k j (H : List (BitVec 64)), C.H <+: H → xs.length - j = k → j ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (lmParams.zip [Enc.idxW n, cellA C o, BitVec.ofNat 64 j,
        BitVec.ofNat 64 xs.length])) lmBody s (pure ((ks.drop j).contains nm)) (PostB (ctxH C H)) := by
  have hlen := hL.small
  have hkl := hL.len
  intro k
  induction k with
  | zero =>
    intro j H hp hk hj
    have hjl : j = xs.length := by omega
    subst hjl
    refine specR_prologue (postB_locals _) (lm_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j H hp hk hj
    have hjl : j < xs.length := by omega
    refine specR_prologue (postB_locals _) (lm_none _ _) ?_
    have hlw := nd_lt_iff j xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, lmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[o + 1 + j]? = some (Enc.idxW xs[j]) := by
      show H[o + 1 + j]? = _
      have := (blkAt_mono hL.blk hp).2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) lmK _ (o + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, lmParams, ctxEnv]; exact cellA_idx C o j) ?_
    refine specR_dropM ?_
    have hfk : denoteNAux s.store.ns (s.store.ns.nodeCount + 1) xs[j] = some (ks[j]'(by omega)) := hL.den j hjl
    refine specR_callPure (C := ctxH C H) lmE NEq.fNeq [NEq.pNa, NEq.pNb] [vv lmK, vv lmN] NEq.neqBody
      [Enc.idxW xs[j], Enc.idxW n] (decide ((ks[j]'(by omega)) = nm)) (by decide) rfl (by decide) hc.neq
      ⟨by simp +decide [Env.get], by simp +decide [Env.get, lmParams, ctxEnv], trivial⟩
      (ExM.PostB (ctxH C H)) (fun b w _ H' => H' = H ∧ w = boolW b)
      (fun b w s' st ⟨hw, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [NEq.pNa, NEq.pNb] _ rfl hlk)
        (NEq.neq_spec (ctxH C H) hc.neq _ xs[j] n nm _ fn s hfk hn))
      (fun w H1 hp1 ⟨eH1, hw⟩ => ?_)
    subst hw; subst H1
    rw [List.drop_eq_getElem_cons (show j < ks.length by omega)]
    by_cases heq : ks[j] = nm
    · refine specR_ifI _ 1 (by simp [sev, boolW, heq]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW, heq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp [sev, boolW, heq]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.contains_cons, beq_false_of_ne (Ne.symm heq), Bool.false_or]
      refine specR_callPure (C := ctxH C H) lmR fLpm lmParams [vv lmN, vv lmP, .op .add [vv lmJ, .const 1], vv lmL]
        lmBody [Enc.idxW n, cellA C o, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 xs.length] ((ks.drop (j + 1)).contains nm)
        (by decide) rfl (by decide) hc.lpm
        ⟨by simp +decide [Env.get, lmParams, ctxEnv], by simp +decide [Env.get, lmParams, ctxEnv],
          by simp +decide [sev, Env.get, lmParams, ctxEnv]; exact word_add1_eq j, by simp +decide [Env.get, lmParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lmParams _ rfl hlk) (ih (j + 1) H hp (by omega) (by omega)))
        (fun w H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp +decide [Env.get]) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


/-- **`lpd`**: every parameter of the level is among the names. -/
theorem lpd_spec (C : Ctx) (hc : LpCodes C) (s : AState) (hwf : LStoreWF s.store.ls) {o : Nat} {xs : List NIdx}
    {ks : List ConLeche.Name} (hL : LpsAt C s o xs ks) :
    ∀ (l : ConLeche.Level) (u : LIdx) (H : List (BitVec 64)), denoteL s.store.ls u = some l → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (ldParams.zip [Enc.idxW u, cellA C o, BitVec.ofNat 64 xs.length])) ldBody s
        (pure (l.allParamsDefined ks)) (PostB (ctxH C H)) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u H hd hp
    refine specR_prologue (postB_locals _) (ld_none _ _) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ldU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, ldParams, ctxEnv]) ?_
    refine specR_lviewPI (C := ctxH C H) u (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW, ConLeche.Level.allParamsDefined], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · obtain ⟨p', he, hda⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' ldA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encSucc] using wordsAt_mem0 P (Enc.idxW a) [] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) ldR fLpd ldParams [vv ldA, vv ldP, vv ldL] ldBody
        [Enc.idxW a, cellA C o, BitVec.ofNat 64 xs.length] (p.allParamsDefined ks) (by decide) rfl (by decide) hc.lpd
        ⟨by simp +decide [Env.get], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk) (ih a H hda hp))
        (fun w H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW (p.allParamsDefined ks)) (by simp +decide [Env.get])
        (fun t ht => ⟨H1, hp1, by simp [ConLeche.Level.allParamsDefined], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- max
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 2
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' ldA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' ldB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) ldR fLpd ldParams [vv ldA, vv ldP, vv ldL] ldBody
        [Enc.idxW a, cellA C o, BitVec.ofNat 64 xs.length] (p.allParamsDefined ks) (by decide) rfl (by decide) hc.lpd
        ⟨by simp +decide [Env.get], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk) (ihp a H hda hp))
        (fun w H1 hp1 hw => ?_)
      subst hw
      cases hpd : p.allParamsDefined ks
      · refine specR_ifI _ 0 (by simp +decide [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        exact specR_returnI _ 0 rfl
          (fun t ht => ⟨H1, hp1, by simp [ConLeche.Level.allParamsDefined, hpd, boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp +decide [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_callPure (C := ctxH C H1) ldR fLpd ldParams [vv ldB, vv ldP, vv ldL] ldBody
          [Enc.idxW b, cellA C o, BitVec.ofNat 64 xs.length] (q.allParamsDefined ks) (by decide) rfl (by decide) hc.lpd
          ⟨by simp +decide [Env.get], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
          (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk) (ihq b H1 hdb (hp.trans hp1)))
          (fun w H2 hp2 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW (q.allParamsDefined ks)) (by simp +decide [Env.get])
          (fun t ht => ⟨H2, hp1.trans hp2, by simp [ConLeche.Level.allParamsDefined, hpd], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- imax
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 3
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' ldA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' ldB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) ldR fLpd ldParams [vv ldA, vv ldP, vv ldL] ldBody
        [Enc.idxW a, cellA C o, BitVec.ofNat 64 xs.length] (p.allParamsDefined ks) (by decide) rfl (by decide) hc.lpd
        ⟨by simp +decide [Env.get], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk) (ihp a H hda hp))
        (fun w H1 hp1 hw => ?_)
      subst hw
      cases hpd : p.allParamsDefined ks
      · refine specR_ifI _ 0 (by simp +decide [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        exact specR_returnI _ 0 rfl
          (fun t ht => ⟨H1, hp1, by simp [ConLeche.Level.allParamsDefined, hpd, boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp +decide [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_callPure (C := ctxH C H1) ldR fLpd ldParams [vv ldB, vv ldP, vv ldL] ldBody
          [Enc.idxW b, cellA C o, BitVec.ofNat 64 xs.length] (q.allParamsDefined ks) (by decide) rfl (by decide) hc.lpd
          ⟨by simp +decide [Env.get], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
          (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk) (ihq b H1 hdb (hp.trans hp1)))
          (fun w H2 hp2 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW (q.allParamsDefined ks)) (by simp +decide [Env.get])
          (fun t ht => ⟨H2, hp1.trans hp2, by simp [ConLeche.Level.allParamsDefined, hpd], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- param
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 4
    · obtain ⟨nm', he, hdn⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' ldA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encParam] using wordsAt_mem0 P (Enc.idxW n) [] []) ?_
      refine specR_ifI _ 1 (by simp +decide [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) ldR fLpm lmParams [vv ldA, vv ldP, .const 0, vv ldL] lmBody
        [Enc.idxW n, cellA C o, BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length] ((ks.drop 0).contains nm) (by decide) rfl
        (by decide) hc.lpm
        ⟨by simp +decide [Env.get], by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu lmParams _ rfl hlk)
          (lpm_spec C hc s hL n nm _ hdn _ 0 H hp rfl (Nat.zero_le _)))
        (fun w H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW ((ks.drop 0).contains nm)) (by simp +decide [Env.get])
        (fun t ht => ⟨H1, hp1, by simp [ConLeche.Level.allParamsDefined], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)


/-- **`lpa`**: every level of the universe list from position `i` on passes `lpd`. -/
theorem lpa_spec (C : Ctx) (hc : LpCodes C) (s : AState) (hwf : LStoreWF s.store.ls) {o : Nat} {xs : List NIdx}
    {ks : List ConLeche.Name} (hL : LpsAt C s o xs ks)
    (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega))) :
    ∀ k i (H : List (BitVec 64)), C.H <+: H → uh.length - i = k → i ≤ uh.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (laParams.zip [Enc.idxW us, cellA C o, BitVec.ofNat 64 xs.length,
        BitVec.ofNat 64 i])) laBody s (pure ((vs.drop i).all (ConLeche.Level.allParamsDefined ks))) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H hp hk hi
    have hi' : i = uh.length := by omega
    subst hi'
    refine specR_prologue (postB_locals _) (la_none _ _) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv laU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, laParams, ctxEnv]) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun vl Pl hvl' _ hvll => ?_)
    rw [huv] at hvl'
    cases hvl'
    have hul : uh.length < 2 ^ 61 := by simpa using hvll
    have hlw := nd_lt_iff uh.length uh.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, laParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i H hp hk hi
    have hil : i < uh.length := by omega
    refine specR_prologue (postB_locals _) (la_none _ _) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv laU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, laParams, ctxEnv]) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun vl Pl hvl' _ hvll => ?_)
    rw [huv] at hvl'
    cases hvl'
    have hul : uh.length < 2 ^ 61 := by simpa using hvll
    have hlw := nd_lt_iff i uh.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, laParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' laA _ (Pl + BitVec.ofNat 64 (8 * i)) (Pl + BitVec.ofNat 64 (8 * i)) (Enc.idxW uh[i])
      (by decide) (by simp +decide [sev, Env.get, laParams, ctxEnv]; rw [Str.w_shl i 3 (by omega), show i * 2 ^ 3 = 8 * i by omega]) rfl
      (by have h := wordsAt_get Pl (uh.map Enc.idxW) i (by simpa using hil) []; simp only [List.getElem_map] at h; exact h) ?_
    refine specR_dropM ?_
    refine specR_callPure (C := ctxH C H) laR fLpd ldParams [vv laA, vv laP, vv laL] ldBody
      [Enc.idxW uh[i], cellA C o, BitVec.ofNat 64 xs.length] ((vs[i]'(by omega)).allParamsDefined ks) (by decide) rfl
      (by decide) hc.lpd
      ⟨by simp +decide [Env.get], by simp +decide [Env.get, laParams, ctxEnv], by simp +decide [Env.get, laParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk)
        (lpd_spec C hc s hwf hL _ uh[i] H (hvd i hil) hp))
      (fun w H1 hp1 hw => ?_)
    subst hw
    rw [List.drop_eq_getElem_cons (show i < vs.length by omega), List.all_cons]
    cases hpd : (vs[i]'(by omega)).allParamsDefined ks
    · refine specR_ifI _ 0 (by simp +decide [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp +decide [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_callPure (C := ctxH C H1) laR fLpa laParams [vv laU, vv laP, vv laL, .op .add [vv laI, .const 1]] laBody
        [Enc.idxW us, cellA C o, BitVec.ofNat 64 xs.length, BitVec.ofNat 64 (i + 1)]
        ((vs.drop (i + 1)).all (ConLeche.Level.allParamsDefined ks)) (by decide) rfl (by decide) hc.lpa
        ⟨by simp +decide [Env.get, laParams, ctxEnv], by simp +decide [Env.get, laParams, ctxEnv],
          by simp +decide [Env.get, laParams, ctxEnv], by simp +decide [sev, Env.get, laParams, ctxEnv]; exact word_add1_eq i, trivial⟩
        (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu laParams _ rfl hlk)
          (ih (i + 1) H1 (hp.trans hp1) (by omega) (by omega)))
        (fun w H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW ((vs.drop (i + 1)).all (ConLeche.Level.allParamsDefined ks))) (by simp +decide [Env.get])
        (fun t ht => ⟨H2, hp1.trans hp2, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
