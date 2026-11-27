import ConPanqueque.T.Ind.ConsCtors

/-!
# `consBlockCtors`: every member's constructors installed

`ccaBody(om, i, n, nP)`: member `i`'s record (slot `i` of the member pointer block at `om`), its former's name
and constructors, `consSumCtors` on them (`csc_spec` from constructor `0`), then itself at `i + 1`, until `i`
reaches `n`.  `cca_spec` refines `consBlockCtors nP (groups.drop i) fe` for the groups `(cvT.name, ctors)` of any
list of members whose constructor names are distinct and fresh.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def ccaOm := ofString "cca_om"
def ccaI := ofString "cca_i"
def ccaN := ofString "cca_n"
def ccaNP := ofString "cca_np"
def ccaMi := ofString "cca_mi"
def ccaOc := ofString "cca_oc"
def ccaT := ofString "cca_t"
def ccaOl := ofString "cca_ol"
def ccaNc := ofString "cca_nc"
def ccaX := ofString "cca_x"
def ccaY := ofString "cca_y"
def fCca := ofString "consBlockCtors"

def ccaParams : List MlS := [ccaOm, ccaI, ccaN, ccaNP]
def ccaLocals : List MlS := [ccaMi, ccaOc, ccaT, ccaOl, ccaNc, ccaX, ccaY]

def ccaBody (C : Ctx) : ProgHOL 64 := prologue ccaLocals
  (.ite (.cmp .lower (vv ccaI) (vv ccaN))
    (.seq (.assign .local ccaMi (.load .one (.op .add [vv ccaOm, .op .add [.panop .mul [vv ccaI, .const 8], .const 8]])))
    (.seq (.assign .local ccaOc (.load .one (vv ccaMi)))
    (.seq (.assign .local ccaT (.load .one (vv ccaOc)))
    (.seq (.assign .local ccaOl (.load .one (.op .add [vv ccaMi, .const 24])))
    (.seq (.assign .local ccaNc (.load .one (vv ccaOl)))
    (.seq (.call (some (some (.local, ccaX), none)) fConsCtors [vv ccaOl, .const 0, vv ccaNc, vv ccaNP, vv ccaT])
    (.seq (.call (some (some (.local, ccaY), none)) fCca [vv ccaOm, .op .add [vv ccaI, .const 1], vv ccaN, vv ccaNP])
      (.return (.const 0)))))))))
    (.return (.const 0)))

structure CCACodes (C : Ctx) : Prop where
  csc : CSCCodes C
  self : C.code.lookup fCca = some (ccaParams.map (fun p => (p, ShapeHOL.one)), ccaBody C, .one)

theorem cca_pure_ok {α : Type} {x a : α} {s s' : AState} (h : (pure x : AM α) s = .ok (a, s')) : a = x ∧ s' = s := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

/-- A member's constructor group, as `consBlockCtors` takes it. -/
def memberGroup (m : MemberShape) : NIdx × List (IConstantVal × Nat) := (m.cvT.name, m.ctors)

theorem find_consSumCtors_ne (nP : Nat) (T : NIdx) :
    ∀ (cs : List (IConstantVal × Nat)) (fe : IFEnv) (n : NIdx), (∀ c ∈ cs, c.1.name ≠ n) →
      (consSumCtors nP T cs fe).find? n = fe.find? n
  | [], _, _, _ => rfl
  | c :: cs, fe, n, h => by
    show (consSumCtors nP T cs (fe.push (.ctorInfo c.1 nP c.2 T))).find? n = _
    rw [find_consSumCtors_ne nP T cs _ n (fun d hd => h d (List.mem_cons_of_mem _ hd)), IFEnv.find?_push]
    have hne : c.1.name ≠ n := h c List.mem_cons_self
    have : ((IConstantInfo.ctorInfo c.1 nP c.2 T).name == n) = false := by
      show (c.1.name == n) = false; simpa using hne
    rw [if_neg (by simp [this])]

/-- The constructor names of all members distinct: member `i`'s distinct, and apart from every later member's. -/
theorem ctorNames_split (ms : List MemberShape) (i : Nat) (hi : i < ms.length)
    (hnd : ((ms.map (·.ctors)).flatten.map (·.1.name)).Nodup) :
    (ms[i].ctors.map (·.1.name)).Nodup ∧
      ∀ c ∈ ms[i].ctors, ∀ m ∈ ms.drop (i + 1), ∀ d ∈ m.ctors, c.1.name ≠ d.1.name := by
  have e : (ms.map (·.ctors)).flatten.map (·.1.name) =
      ((ms.take i).map (·.ctors)).flatten.map (·.1.name) ++ ((ms.drop i).map (·.ctors)).flatten.map (·.1.name) := by
    conv_lhs => rw [← List.take_append_drop i ms]
    simp only [List.map_append, List.flatten_append]
  rw [e] at hnd
  have h := (List.nodup_append.mp hnd).2.1
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.map_append, List.nodup_append] at h
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨h1, fun c hc m hm d hd => ?_⟩
  exact h3 _ (List.mem_map_of_mem hc) _
    (List.mem_map_of_mem (List.mem_flatten.mpr ⟨m.ctors, List.mem_map_of_mem hm, hd⟩))

section
variable {σ : Type}

theorem cca_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ccaLocals → (ctxEnv C ++ ccaParams.zip vals).get x = none :=
  Knot.params_none C ccaLocals ccaParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`consBlockCtors`** over the members from `i` on. -/
theorem cca_spec (C : Ctx) (hc : CCACodes C) (nP : Nat) (hnP : nP < 2 ^ 63) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58)
    (hcl : ∀ m ∈ ms, m.ctors.length < 2 ^ 58) (hden : ∀ m ∈ ms, ∀ c ∈ m.ctors, CVDen c.1 C.St)
    (hnd : ((ms.map (·.ctors)).flatten.map (·.1.name)).Nodup) :
    ∀ f i (fe : IFEnv) (EH : List (BitVec 64)) envM (H : List (BitVec 64)) (s : AState),
      ms.length - i = f → i ≤ ms.length → C.H <+: H → C.EH <+: EH → CtxOK (ctxNew C fe EH envM H) →
      TblGate fe → FlagsOK fe → LitsPinned fe C.pins → (∀ m ∈ ms.drop i, ∀ c ∈ m.ctors, fe.find? c.1.name = none) →
      SpecR (σ := σ) (Pre (ctxNew C fe EH envM H) s (ccaParams.zip [cellA C om, BitVec.ofNat 64 i,
          BitVec.ofNat 64 ms.length, BitVec.ofNat 64 nP])) (ccaBody C) s
        (pure (consBlockCtors nP ((ms.map memberGroup).drop i) fe)) (PostEnv C) := by
  intro f
  induction f with
  | zero =>
    intro i fe EH envM H s hf hi hpH hpE hok hg hF hL hnew
    have hil : i = ms.length := by omega
    subst hil
    refine specR_prologue (postEnv_locals _) (cca_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ccaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [show (ms.map memberGroup).drop ms.length = [] by simp]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, envM, H, hpE, hpH, hok, sr_of_eq ht.sr rfl rfl rfl rfl, hg, hF, hL⟩)
  | succ f ih =>
    intro i fe EH envM H s hf hi hpH hpE hok hg hF hL hnew
    have hil : i < ms.length := by omega
    refine specR_prologue (postEnv_locals _) (cca_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, ccaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨mi, hmi, hrep⟩ := hM.2 i hil
    obtain ⟨⟨oc, hoc, hcv⟩, -, -, ⟨ol, hol, hctr⟩⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) ccaMi _ (om + 1 + i) _ (get_prefix hmi hpH) (by decide)
      (by simp +decide [sev, Env.get, ccaParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) ccaOc (vv ccaMi) mi _ (get_prefix hoc hpH) (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) ccaT (vv ccaOc) oc _ (get_prefix hcv.1 hpH) (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) ccaOl _ (mi + 3) _ (get_prefix hol hpH) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C mi 3) ?_
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) ccaNc (vv ccaOl) ol _ (get_prefix hctr.1 hpH) (by decide)
      (by simp [sev, Env.get_cons]; rfl) ?_
    have hmem : ms[i] ∈ ms := List.getElem_mem hil
    obtain ⟨hnd1, hdisj⟩ := ctorNames_split ms i hil hnd
    have hgi : (ms.map memberGroup).drop i =
        memberGroup ms[i] :: (ms.map memberGroup).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hil)]; simp
    rw [hgi]
    refine specR_congr (m' := (pure (consSumCtors nP ms[i].cvT.name (ms[i].ctors.drop 0) fe) : AM IFEnv) >>= fun fe' =>
        (pure (consBlockCtors nP ((ms.map memberGroup).drop (i + 1)) fe') : AM IFEnv))
      (by simp [consBlockCtors, memberGroup]) ?_
    have hnew0 : ∀ c ∈ ms[i].ctors.drop 0, fe.find? c.1.name = none := fun c hc =>
      hnew ms[i] (by rw [List.drop_eq_getElem_cons hil]; exact List.mem_cons_self) c (by simpa using hc)
    refine specR_callNC (C := ctxNew C fe EH envM H) (D := ctxLocals ++ ccaLocals) ccaX fConsCtors cscParams
      [vv ccaOl, .const 0, vv ccaNc, vv ccaNP, vv ccaT] (cscBody C)
      [cellA C ol, BitVec.ofNat 64 0, BitVec.ofNat 64 ms[i].ctors.length, BitVec.ofNat 64 nP, Enc.idxW ms[i].cvT.name]
      (by decide) rfl (by decide) hc.csc.self ?_
      (fun a w s' st => (pure (consSumCtors nP ms[i].cvT.name (ms[i].ctors.drop 0) fe) : AM IFEnv) s = .ok (a, s') ∧
        PostEnv C a w s' st)
      (fun r w s' C' => r = consSumCtors nP ms[i].cvT.name (ms[i].ctors.drop 0) fe ∧
        ∃ EH envM H, C' = ctxNew C r EH envM H ∧ C.EH <+: EH ∧ C.H <+: H ∧
        CtxOK (ctxNew C r EH envM H) ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins)
      (fun r w s' st ⟨hr, EH, envM, H, h1, h2, h3, h4, h5⟩ =>
        ⟨_, ⟨(cca_pure_ok hr).1, EH, envM, H, rfl, h1, h2, h3, h5⟩, h4⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cscParams _ rfl hlk)
        (csc_spec C hc.csc nP hnP ms[i].cvT.name ms[i].ctors ol hctr (hcl _ hmem) (hden _ hmem) hnd1
          _ 0 fe EH envM H s rfl (Nat.zero_le _) hpH hpE hok hg hF hL hnew0)))
      (fun r w s6 C6 ⟨er, EH7, envM7, H7, eC, h1, h2, h3, h4, h5, h6⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, ccaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    subst eC
    have hnew' : ∀ m ∈ ms.drop (i + 1), ∀ c ∈ m.ctors, r.find? c.1.name = none := by
      intro m hm c hc
      rw [er, List.drop_zero, find_consSumCtors_ne nP _ _ _ _ (fun d hd e => hdisj d hd m hm c hc e)]
      exact hnew m (by rw [List.drop_eq_getElem_cons hil]; exact List.mem_cons_of_mem _ hm) c hc
    refine specR_congr (m' := (pure (consBlockCtors nP ((ms.map memberGroup).drop (i + 1)) r) : AM IFEnv) >>=
        fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNC (C := ctxNew C r EH7 envM7 H7) (D := ctxLocals ++ ccaLocals) ccaY fCca ccaParams
      [vv ccaOm, .op .add [vv ccaI, .const 1], vv ccaN, vv ccaNP] (ccaBody C)
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length, BitVec.ofNat 64 nP]
      (by decide) rfl (by decide) hc.self ?_
      (PostEnv C) (fun r w s' C' => ∃ EH envM H, C' = ctxNew C r EH envM H ∧ C.EH <+: EH ∧ C.H <+: H ∧
        CtxOK (ctxNew C r EH envM H) ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins)
      (fun r w s' st ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, rfl, h1, h2, h3, h5⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccaParams _ rfl hlk)
        (ih (i + 1) r EH7 envM7 H7 s6 (by omega) (by omega) h2 h1 h3 h4 h5 h6 hnew'))
      (fun r' w s7 C7 ⟨EH8, envM8, H8, eC, g1, g2, g3, g4⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, ccaParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, ccaParams, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, ccaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ccaParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH8, envM8, H8, g1, g2, g3, sr_of_eq ht.sr rfl rfl rfl rfl, g4⟩)

end

end ConPanqueque.T.Ind
