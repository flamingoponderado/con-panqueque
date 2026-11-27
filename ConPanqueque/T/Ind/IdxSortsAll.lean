import ConPanqueque.T.Ind.IdxSorts

/-!
# `checkBlockIdxSorts` at any number of members

`bsaBody(ms, i, n, nP, sr)`: member `i` (`bis` on the pointer-block cell `ms + 8 i`, whose successor cell
points to member `i`'s record), then itself at `i + 1`, until `i` reaches `n`.  `bsa_spec` refines
`checkBlockIdxSorts mode fe p (p.members.drop i)` by induction on the members left.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def bsaMs := ofString "bsa_ms"
def bsaI := ofString "bsa_i"
def bsaN := ofString "bsa_n"
def bsaNP := ofString "bsa_np"
def bsaSr := ofString "bsa_sr"
def bsaX := ofString "bsa_x"
def bsaY := ofString "bsa_y"
def fBsa := ofString "checkBlockIdxSortsAll"

def bsaParams : List MlS := [bsaMs, bsaI, bsaN, bsaNP, bsaSr]
def bsaLocals : List MlS := [bsaX, bsaY]

def bsaBody : ProgHOL 64 := prologue bsaLocals
  (.ite (.cmp .lower (vv bsaI) (vv bsaN))
    (.seq (.call (some (some (.local, bsaX), none)) fBis
        [.op .add [vv bsaMs, .panop .mul [vv bsaI, .const 8]], vv bsaNP, vv bsaSr])
    (.seq (.call (some (some (.local, bsaY), none)) fBsa
        [vv bsaMs, .op .add [vv bsaI, .const 1], vv bsaN, vv bsaNP, vv bsaSr])
      (.return (.const 0))))
    (.return (.const 0)))

structure BSACodes (C : Ctx) : Prop where
  bis : BISCodes C
  self : C.code.lookup fBsa = some (bsaParams.map (fun p => (p, ShapeHOL.one)), bsaBody, .one)

theorem cellA_mul8 (C : Ctx) (o i : Nat) (hi : i < 2 ^ 61) :
    cellA C o + BitVec.ofNat 64 i * 8#64 = cellA C (o + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

section
variable {σ : Type}

theorem bsa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bsaLocals → (ctxEnv C ++ bsaParams.zip vals).get x = none :=
  Knot.params_none C bsaLocals bsaParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`checkBlockIdxSorts`** over the members from `i` on. -/
theorem bsa_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : BSACodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (p : BlockShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (hml : p.members.length < 2 ^ 58) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls p.resSort = some lsr)
    (hnP : p.nP < 2 ^ 56) (hni : ∀ ms ∈ p.members, ms.nIdx < 2 ^ 56) :
    ∀ f i (H : List (BitVec 64)) (s : AState), p.members.length - i = f → i ≤ p.members.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (bsaParams.zip [cellA C om, BitVec.ofNat 64 i,
        BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP, Enc.idxW p.resSort])) bsaBody s
        (checkBlockIdxSorts mode C.fe p (p.members.drop i)) (Decl.PostU (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = p.members.length := by omega
    subst hin
    refine specR_prologue (Decl.postU_locals _) (bsa_none _ _) ?_
    have hlw := nd_lt_iff p.members.length p.members.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, bsaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < p.members.length := by omega
    refine specR_prologue (Decl.postU_locals _) (bsa_none _ _) ?_
    have hlw := nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bsaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin]
    have hstep : checkBlockIdxSorts mode C.fe p (p.members[i] :: p.members.drop (i + 1)) =
        checkBlockIdxSorts mode C.fe p [p.members[i]] >>= fun _ =>
          checkBlockIdxSorts mode C.fe p (p.members.drop (i + 1)) := by
      simp only [checkBlockIdxSorts, bind_assoc, pure_bind]
    rw [hstep]
    obtain ⟨oi, hoi, hrep⟩ := hM.2 i hin
    have hok1 := ctxOK_H hok H
    refine specR_callNIH (C := ctxH C H) bsaX fBis bisParams
      [.op .add [vv bsaMs, .panop .mul [vv bsaI, .const 8]], vv bsaNP, vv bsaSr] (bisBody C)
      [cellA C (om + i), BitVec.ofNat 64 p.nP, Enc.idxW p.resSort] (by decide) rfl (by decide) hc.bis.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv]; exact cellA_mul8 C om i (by omega),
        by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bisParams _ rfl hlk)
        (bis_spec1 mode ra (ctxH C H) hok1 hs (by ctx_tr hk) (by ctx_tr hac) (by ctx_tr hc.bis) (fun H' => heqS H') p p.members[i] (om + i)
          ⟨oi, getElem?_prefix hp (by rw [show om + i + 1 = om + 1 + i by omega]; exact hoi), memberRep_mono hp hrep⟩ lsr hSd
          hnP (hni _ (List.getElem_mem _)) s))
      (fun r w s2 H2 hp2 _ => ?_)
    have hp2' : H <+: H2 := hp2
    refine specR_congr (m' := checkBlockIdxSorts mode C.fe p (p.members.drop (i + 1)) >>= fun r => pure r)
      (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) bsaY fBsa bsaParams
      [vv bsaMs, .op .add [vv bsaI, .const 1], vv bsaN, vv bsaNP, vv bsaSr] bsaBody
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP,
        Enc.idxW p.resSort] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, bsaParams, ctxEnv], trivial⟩
      (Decl.PostU (ctxH C H2)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bsaParams _ rfl hlk)
        (ih (i + 1) H2 s2 (by omega) (by omega) (hp.trans hp2')))
      (fun r w s3 H3 hp3 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp2'.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
