import ConPanqueque.T.Ind.RecInstall

/-!
# Every recursor of an unnested block installed

`riaBody(or, i, n)`: recursor `i` (slot `i` of the recursor pointer block at `or`) installed by `rin` (its rules
firing plainly; a name already present hangs), then itself at `i + 1`, until `i` reaches `n`.  `ria_spec` refines
`pure (fe.pushAll ((recs.drop i).map plainRec))`; `blockRecs_plain` is the twin's `blockRecs` at a block whose
recursors all target a member (`tgt < k`, every unnested block), so the two agree there.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def riaOr := ofString "ria_or"
def riaI := ofString "ria_i"
def riaN := ofString "ria_n"
def riaRo := ofString "ria_ro"
def riaX := ofString "ria_x"
def riaY := ofString "ria_y"
def fRia := ofString "recInstallAll"

def riaParams : List MlS := [riaOr, riaI, riaN]
def riaLocals : List MlS := [riaRo, riaX, riaY]

def riaBody : ProgHOL 64 := prologue riaLocals
  (.ite (.cmp .lower (vv riaI) (vv riaN))
    (.seq (.assign .local riaRo (.load .one (.op .add [vv riaOr, .op .add [.panop .mul [vv riaI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, riaX), none)) fRin [vv riaRo])
    (.seq (.call (some (some (.local, riaY), none)) fRia [vv riaOr, .op .add [vv riaI, .const 1], vv riaN])
      (.return (.const 0)))))
    (.return (.const 0)))

structure RIACodes (C : Ctx) : Prop where
  rin : RINCodes C
  self : C.code.lookup fRia = some (riaParams.map (fun p => (p, ShapeHOL.one)), riaBody, .one)

/-- **The twin's recursors at an unnested block**: every recursor targets a member, so each fires plainly. -/
theorem blockRecs_plain (p : BlockShape) :
    ∀ (rcs : List RecShape), (∀ rc ∈ rcs, rc.tgt < p.k) → blockRecs p rcs = pure (rcs.map plainRec)
  | [], _ => rfl
  | rc :: rest, h => by
    have ht := h rc List.mem_cons_self
    simp only [blockRecs, recFire, ht, ↓reduceIte, pure_bind,
      blockRecs_plain p rest (fun r hr => h r (List.mem_cons_of_mem _ hr)), List.map_cons, plainRec]

section
variable {σ : Type}

theorem ria_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ riaLocals → (ctxEnv C ++ riaParams.zip vals).get x = none :=
  Knot.params_none C riaLocals riaParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **The recursors from `i` on installed**, each firing plainly. -/
theorem ria_spec (C : Ctx) (hc : RIACodes C) (rcs : List RecShape) (orr : Nat)
    (hR : PtrsRep C C.H orr (RecRep C C.H) rcs) (hrl : rcs.length < 2 ^ 58)
    (hlps : ∀ rc ∈ rcs, rc.cvR.levelParams.length < 2 ^ 60) (hden : ∀ rc ∈ rcs, CVDen rc.cvR C.St) :
    ∀ f i (fe : IFEnv) (EH : List (BitVec 64)) envM (H : List (BitVec 64)) (s : AState),
      rcs.length - i = f → i ≤ rcs.length → C.H <+: H → C.EH <+: EH → CtxOK (ctxNew C fe EH envM H) →
      TblGate fe → FlagsOK fe → LitsPinned fe C.pins →
      SpecR (σ := σ) (Pre (ctxNew C fe EH envM H) s (riaParams.zip [cellA C orr, BitVec.ofNat 64 i,
          BitVec.ofNat 64 rcs.length])) riaBody s
        (pure (IFEnv.pushAll ((rcs.drop i).map plainRec) fe)) (PostEnv C) := by
  intro f
  induction f with
  | zero =>
    intro i fe EH envM H s hf hi hpH hpE hok hg hF hL
    have hil : i = rcs.length := by omega
    subst hil
    refine specR_prologue (postEnv_locals _) (ria_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff rcs.length rcs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, riaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, envM, H, hpE, hpH, hok, sr_of_eq ht.sr rfl rfl rfl rfl, hg, hF, hL⟩)
  | succ f ih =>
    intro i fe EH envM H s hf hi hpH hpE hok hg hF hL
    have hil : i < rcs.length := by omega
    refine specR_prologue (postEnv_locals _) (ria_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i rcs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, riaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨ro, hro, hrep⟩ := hR.2 i hil
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) riaRo _ (orr + 1 + i) _ (get_prefix hro hpH) (by decide)
      (by simp +decide [sev, Env.get, riaParams, ctxEnv]; exact cellA_mulIdx C orr i (by omega)) ?_
    have hmem : rcs[i] ∈ rcs := List.getElem_mem hil
    rw [List.drop_eq_getElem_cons hil, List.map_cons]
    refine specR_congr (m' := (pure ((ctxNew C fe EH envM H).fe.push (plainRec rcs[i])) : AM IFEnv) >>= fun fe' =>
        (pure (IFEnv.pushAll ((rcs.drop (i + 1)).map plainRec) fe') : AM IFEnv)) (by simp [IFEnv.pushAll]; rfl) ?_
    refine specR_callNC (C := ctxNew C fe EH envM H) (D := ctxLocals ++ riaLocals) riaX fRin rinParams
      [vv riaRo] (rinBody C) [cellA C ro] (by decide) rfl (by decide) hc.rin.self ?_
      (fun a w s' st => (pure ((ctxNew C fe EH envM H).fe.push (plainRec rcs[i])) : AM IFEnv) s = .ok (a, s') ∧
        PostEnv (ctxNew C fe EH envM H) a w s' st)
      (fun r w s' C' => r = fe.push (plainRec rcs[i]) ∧
        ∃ EH envM H, C' = ctxNew C r EH envM H ∧ C.EH <+: EH ∧ C.H <+: H ∧
        CtxOK (ctxNew C r EH envM H) ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins)
      (fun r w s' st ⟨hr, EH', envM', H', h1, h2, h3, h4, h5⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, -⟩ := hr
        exact ⟨_, ⟨rfl, EH', envM', H', rfl, hpE.trans h1, hpH.trans h2, h3, h5⟩, h4⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rinParams _ rfl hlk)
        (rin_spec (ctxNew C fe EH envM H) hok (by ctx_tr hc.rin) hg hF hL rcs[i] ro (recRep_mono hpH hrep)
          (hlps _ hmem) (hden _ hmem) s)))
      (fun r w s6 C6 ⟨er, EH7, envM7, H7, eC, h1, h2, h3, h4, h5, h6⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    subst eC er
    refine specR_congr (m' := (pure (IFEnv.pushAll ((rcs.drop (i + 1)).map plainRec) (fe.push (plainRec rcs[i]))) :
        AM IFEnv) >>= fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNC (C := ctxNew C (fe.push (plainRec rcs[i])) EH7 envM7 H7) (D := ctxLocals ++ riaLocals) riaY fRia
      riaParams [vv riaOr, .op .add [vv riaI, .const 1], vv riaN] riaBody
      [cellA C orr, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rcs.length]
      (by decide) rfl (by decide) hc.self ?_
      (PostEnv C) (fun r w s' C' => ∃ EH envM H, C' = ctxNew C r EH envM H ∧ C.EH <+: EH ∧ C.H <+: H ∧
        CtxOK (ctxNew C r EH envM H) ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins)
      (fun r w s' st ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, rfl, h1, h2, h3, h5⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu riaParams _ rfl hlk)
        (ih (i + 1) _ EH7 envM7 H7 s6 (by omega) (by omega) h2 h1 h3 h4 h5 h6))
      (fun r' w s7 C7 ⟨EH8, envM8, H8, eC, g1, g2, g3, g4⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, riaParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, riaParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, riaParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH8, envM8, H8, g1, g2, g3, sr_of_eq ht.sr rfl rfl rfl rfl, g4⟩)

end

end ConPanqueque.T.Ind
