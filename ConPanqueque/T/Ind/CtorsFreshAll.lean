import ConPanqueque.T.Ind.CtorsFresh

/-!
# Every member's constructors fresh in the environment (else hang)

`cfaBody(om, i, n)`: member `i`'s constructors (`cfh` from constructor `0`), then itself at `i + 1`, until `i`
reaches `n`.  Pure: the state is kept.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cfaOm := ofString "cfa_om"
def cfaI := ofString "cfa_i"
def cfaN := ofString "cfa_n"
def cfaMi := ofString "cfa_mi"
def cfaOl := ofString "cfa_ol"
def cfaNc := ofString "cfa_nc"
def cfaX := ofString "cfa_x"
def cfaY := ofString "cfa_y"
def fCfa := ofString "ctorsFreshAll"

def cfaParams : List MlS := [cfaOm, cfaI, cfaN]
def cfaLocals : List MlS := [cfaMi, cfaOl, cfaNc, cfaX, cfaY]

def cfaBody : ProgHOL 64 := prologue cfaLocals
  (.ite (.cmp .lower (vv cfaI) (vv cfaN))
    (.seq (.assign .local cfaMi (.load .one (.op .add [vv cfaOm, .op .add [.panop .mul [vv cfaI, .const 8], .const 8]])))
    (.seq (.assign .local cfaOl (.load .one (.op .add [vv cfaMi, .const 24])))
    (.seq (.assign .local cfaNc (.load .one (vv cfaOl)))
    (.seq (.call (some (some (.local, cfaX), none)) fCfh [vv cfaOl, .const 0, vv cfaNc])
    (.seq (.call (some (some (.local, cfaY), none)) fCfa [vv cfaOm, .op .add [vv cfaI, .const 1], vv cfaN])
      (.return (.const 0)))))))
    (.return (.const 0)))

structure CFACodes (C : Ctx) : Prop where
  cfh : CFHCodes C
  self : C.code.lookup fCfa = some (cfaParams.map (fun p => (p, ShapeHOL.one)), cfaBody, .one)

section
variable {σ : Type}

theorem cfa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfaLocals → (ctxEnv C ++ cfaParams.zip vals).get x = none :=
  Knot.params_none C cfaLocals cfaParams vals (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- **The constructors of the members from `i` on are fresh** (a stored one hangs). -/
theorem cfa_spec (C : Ctx) (hok : CtxOK C) (hc : CFACodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58)
    (hcl : ∀ m ∈ ms, m.ctors.length < 2 ^ 58) :
    ∀ f i (s : AState), ms.length - i = f → i ≤ ms.length →
      SpecR (σ := σ) (Pre C s (cfaParams.zip [cellA C om, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length])) cfaBody s
        (pure ()) (PostKF C s (∀ m ∈ ms.drop i, ∀ c ∈ m.ctors, C.fe.find? c.1.name = none)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = ms.length := by omega
    subst hil
    refine specR_prologue (postKF_locals _ _ _) (cfa_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, cfaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < ms.length := by omega
    refine specR_prologue (postKF_locals _ _ _) (cfa_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, cfaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨mi, hmi, hrep⟩ := hM.2 i hil
    obtain ⟨-, -, -, ⟨ol, hol, hctr⟩⟩ := hrep
    refine UD.specR_heapLoadI' (C := C) cfaMi _ (om + 1 + i) _ hmi (by decide)
      (by simp +decide [sev, Env.get, cfaParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) cfaOl _ (mi + 3) _ hol (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C mi 3) ?_
    refine UD.specR_heapLoadI' (C := C) cfaNc (vv cfaOl) ol _ hctr.1 (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM cfaX fCfh cfhParams [vv cfaOl, .const 0, vv cfaNc] (cfhBody C)
      [cellA C ol, BitVec.ofNat 64 0, BitVec.ofNat 64 ms[i].ctors.length] (by decide) rfl (by decide) hc.cfh.self
      ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (PostKF C s (∀ c ∈ ms[i].ctors.drop 0, C.fe.find? c.1.name = none)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfhParams _ rfl hlk)
        (cfh_spec C hok hc.cfh ms[i].ctors ol hctr (hcl _ (List.getElem_mem hil)) _ 0 s rfl (Nat.zero_le _)))
      (fun _ w s1 st ⟨hs1, h0, _⟩ => ?_)
    subst s1
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM cfaY fCfa cfaParams [vv cfaOm, .op .add [vv cfaI, .const 1], vv cfaN] cfaBody
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cfaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfaParams, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, cfaParams, ctxEnv], trivial⟩
      (PostKF C s (∀ m ∈ ms.drop (i + 1), ∀ c ∈ m.ctors, C.fe.find? c.1.name = none)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfaParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s2 st ⟨hs2, hall, _⟩ => ?_)
    subst s2
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro m hm c hc'
      rcases List.mem_cons.mp hm with e | e
      · subst e; exact h0 c (by simpa using hc')
      · exact hall m e c hc', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
