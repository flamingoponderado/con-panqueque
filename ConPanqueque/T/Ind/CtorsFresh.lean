import ConPanqueque.T.Ind.RecInstall
import ConPanqueque.T.Ind.KindsFlat

/-!
# The constructors' names fresh in the environment (else hang)

`cfhBody`: each constructor's name (a `CtorsRep` block) looked up in the constant table; a hit hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

theorem nameNodup_nodup : ∀ {xs : List NIdx}, nameNodup xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nameNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nameNodup_nodup h.2⟩
    have := h.1
    simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at this
    exact this x hm rfl

def cfhQ := ofString "cfh_q"
def cfhI := ofString "cfh_i"
def cfhN := ofString "cfh_n"
def cfhX := ofString "cfh_x"
def cfhNm := ofString "cfh_nm"
def cfhY := ofString "cfh_y"
def cfhR := ofString "cfh_r"
def fCfh := ofString "ctorsFresh"

def cfhParams : List MlS := [cfhQ, cfhI, cfhN]
def cfhLocals : List MlS := [cfhX, cfhNm, cfhY, cfhR]

def cfhBody (C : Ctx) : ProgHOL 64 := prologue cfhLocals
  (.ite (.cmp .lower (vv cfhI) (vv cfhN))
    (.seq (.assign .local cfhX (.load .one (.op .add [vv cfhQ, .op .add [.panop .mul [vv cfhI, .const 16], .const 8]])))
    (.seq (.assign .local cfhNm (.load .one (vv cfhX)))
    (envFindP C cfhY (vv cfhNm)
    (.ite (.cmp .notEqual (vv cfhY) (.const 0)) hang
    (.seq (.call (some (some (.local, cfhR), none)) fCfh [vv cfhQ, .op .add [vv cfhI, .const 1], vv cfhN])
      (.return (.const 0)))))))
    (.return (.const 0)))

structure CFHCodes (C : Ctx) : Prop where
  g : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  p : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  self : C.code.lookup fCfh = some (cfhParams.map (fun p => (p, ShapeHOL.one)), cfhBody C, .one)

section
variable {σ : Type}

theorem cfh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfhLocals → (ctxEnv C ++ cfhParams.zip vals).get x = none :=
  Knot.params_none C cfhLocals cfhParams vals (by decide) (by decide)

/-- **The constructors from position `i` on are fresh** (a stored one hangs). -/
theorem cfh_spec (C : Ctx) (hok : CtxOK C) (hc : CFHCodes C)
    (cs : List (IConstantVal × Nat)) (oq : Nat) (hcr : CtorsRep C C.H oq cs) (hcl : cs.length < 2 ^ 58) :
    ∀ f i (s : AState), cs.length - i = f → i ≤ cs.length →
      SpecR (σ := σ) (Pre C s (cfhParams.zip [cellA C oq, BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length])) (cfhBody C) s
        (pure ()) (PostKF C s (∀ c ∈ cs.drop i, C.fe.find? c.1.name = none)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = cs.length := by omega
    subst hil
    refine specR_prologue (postKF_locals _ _ _) (cfh_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff cs.length cs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, cfhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < cs.length := by omega
    refine specR_prologue (postKF_locals _ _ _) (cfh_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, cfhParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, h1, hcv, -⟩ := hcr.2 i hil
    refine UD.specR_heapLoadI' (C := C) cfhX _ (oq + 1 + 2 * i) _ h1 (by decide)
      (by simp +decide [sev, Env.get, cfhParams, ctxEnv]; exact cellA_pair1 C oq i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) cfhNm (vv cfhX) oc _ hcv.1 (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_envFindI hok hc.g hc.p cfhY (vv cfhNm) cs[i].1.name (by decide) (by simp +decide [sev, Env.get_cons])
      (by simp +decide [Env.get_cons, Env.get, cfhParams, ctxEnv]) ?_
    have hrel := find_rel hok cs[i].1.name
    revert hrel
    rcases hfn : C.fe.find? cs[i].1.name with _ | ci0
    swap
    · intro ⟨o', hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    intro hrel
    simp only at hrel
    rw [hrel]
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM cfhR fCfh cfhParams [vv cfhQ, .op .add [vv cfhI, .const 1], vv cfhN] (cfhBody C)
      [cellA C oq, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cfhParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cfhParams, ctxEnv]; exact e_succ i,
        by simp +decide [sev, Env.get_cons, Env.get, cfhParams, ctxEnv], trivial⟩
      (PostKF C s (∀ c ∈ cs.drop (i + 1), C.fe.find? c.1.name = none)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfhParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s1 st ⟨hs1, hall, _⟩ => ?_)
    subst s1
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by
      rw [List.drop_eq_getElem_cons hil]
      intro c hc'
      rcases List.mem_cons.mp hc' with e | e
      · subst e; exact hfn
      · exact hall c e, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
