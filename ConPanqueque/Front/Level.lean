import ConPanqueque.Front.RetCall
import ConPanqueque.T.LInternLv
import ConRon.Arena.Frontend.ExportC

/-! # Level records into the store (`parseLevelEntryD`)

A level record binds a fresh stream index to an interned level node whose children are read from
the level (or name) table.  Each case is: the freshness test, the table reads, the ported intern
procedure, the table write.  The result is the twin's `parseLevelEntryD`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable LevelRec)

variable {σ : Type}

def fx := ofString "fx"
def fy := ofString "fy"
def fz := ofString "fz"
def fh := ofString "fh"
def fTL := ofString "ftl"
def fTN := ofString "ftn"
def fCap := ofString "fcap"
def fI := ofString "fi"
def fU := ofString "fu"
def fV2 := ofString "fv"

theorem Env.get_cons (Γ : Env) (y x : MlS) (v : BitVec 64) :
    Env.get ((y, v) :: Γ) x = if x = y then some v else Env.get Γ x := rfl

/-- After a level record: the new store is represented with the level table's cell written, and the
other parts of the parse state are as they were. -/
def LvPost (C : Ctx) (jL cap : Nat) (st : StateD) (i : Nat) :
    StateD → BitVec 64 → AState → PState σ → Prop :=
  fun st' _ s' t' => ∃ w', SR (ctxH C (C.H.set (jL + i) w')) s' t' ∧
    TblRel (C.H.set (jL + i) w') jL cap st'.levels ∧
    st'.names = st.names ∧ st'.exprs = st.exprs ∧ st'.decls = st.decls

/-- `succ u` at index `i`. -/
def lvSuccP : ProgHOL 64 :=
  tblFreshP fx (vv fTL) (vv fCap) (vv fI)
    (tblGetP fy (vv fTL) (vv fCap) (vv fU)
      (.seq (.call (some (some (.local, fh), none)) fInternLSucc [vv fy])
        (tblSetP (vv fTL) (vv fI) (vv fh) (.return (.const 0)))))

theorem lvSucc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fh], x ∈ D)
    (st : StateD) (jL cap : Nat) (hrel : TblRel C.H jL cap st.levels) (hcap : 8 * cap < 2 ^ 64)
    (i u : Nat) (hi : i < 2 ^ 64) (hu : u < 2 ^ 64)
    (hTL : Γ.get fTL = some (cellA C jL)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 u)) :
    SpecR (Inv (σ := σ) C s Γ M D) lvSuccP s (parseLevelEntryD st i (.succ u)) (LvPost C jL cap st i) := by
  unfold lvSuccP
  refine specR_tblFreshI fx (hD fx (by simp)) jL cap st.levels hrel hcap (vv fTL) (vv fCap) (vv fI)
    (by simpa [sev, vv] using hTL) (by simpa [sev, vv] using hC) i hi (by simpa [sev, vv] using hI)
    (fun hic hg => ?_)
  have hm : parseLevelEntryD st i (.succ u) =
      (st.level u >>= fun lu => internLNode (.succ lu) >>= fun l =>
        (pure { st with levels := st.levels.insert i l } : AM StateD)) := by
    simp [parseLevelEntryD, StateD.freshLevel, IdTable.bound_eq, hg]
  rw [hm]
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fy (hD fy (by simp)) jL cap st.levels hrel hcap (vv fTL) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTL)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) u hu
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun lu hlu => ?_)
  have hm2 : (st.level u >>= fun lu => internLNode (.succ lu) >>= fun l =>
        (pure { st with levels := st.levels.insert i l } : AM StateD)) =
      (internLNode (.succ lu) >>= fun l => (pure { st with levels := st.levels.insert i l } : AM StateD)) := by
    simp [StateD.level, hlu]
  rw [hm2]
  refine callLN fh fInternLSucc [lEu] [vv fy] internLSuccBody [Enc.idxW lu] (by decide) rfl (hD fh (by simp)) hcS
    ⟨by simp [sev, vv, Env.get_cons], trivial⟩ (.succ lu) (internLSucc_body_spec ra C hok s lu)
    (fun h s' _ => ?_)
  have g2 : ∀ y, y ≠ fh → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fy, Enc.idxW lu) :: (fy, Enc.idxW lu + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  refine specR_tblSetI hok jL cap st.levels hrel hcap (vv fTL) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide) (by decide)]; exact hTL) i hic h
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- `param n` at index `i` (the name from the name table). -/
def lvParamP : ProgHOL 64 :=
  tblFreshP fx (vv fTL) (vv fCap) (vv fI)
    (tblGetP fy (vv fTN) (vv fCap) (vv fU)
      (.seq (.call (some (some (.local, fh), none)) fInternLParam [vv fy])
        (tblSetP (vv fTL) (vv fI) (vv fh) (.return (.const 0)))))

theorem lvParam_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fh], x ∈ D)
    (st : StateD) (jL jN cap : Nat) (hrel : TblRel C.H jL cap st.levels) (hreln : TblRel C.H jN cap st.names)
    (hcap : 8 * cap < 2 ^ 64) (i u : Nat) (hi : i < 2 ^ 64) (hu : u < 2 ^ 64)
    (hTL : Γ.get fTL = some (cellA C jL)) (hTN : Γ.get fTN = some (cellA C jN))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 u)) :
    SpecR (Inv (σ := σ) C s Γ M D) lvParamP s (parseLevelEntryD st i (.param u)) (LvPost C jL cap st i) := by
  unfold lvParamP
  refine specR_tblFreshI fx (hD fx (by simp)) jL cap st.levels hrel hcap (vv fTL) (vv fCap) (vv fI)
    (by simpa [sev, vv] using hTL) (by simpa [sev, vv] using hC) i hi (by simpa [sev, vv] using hI)
    (fun hic hg => ?_)
  have hm : parseLevelEntryD st i (.param u) =
      (st.name u >>= fun n => internLNode (.param n) >>= fun l =>
        (pure { st with levels := st.levels.insert i l } : AM StateD)) := by
    simp [parseLevelEntryD, StateD.freshLevel, IdTable.bound_eq, hg]
  rw [hm]
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTN)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) u hu
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun n hn => ?_)
  have hm2 : (st.name u >>= fun n => internLNode (.param n) >>= fun l =>
        (pure { st with levels := st.levels.insert i l } : AM StateD)) =
      (internLNode (.param n) >>= fun l => (pure { st with levels := st.levels.insert i l } : AM StateD)) := by
    simp [StateD.name, hn]
  rw [hm2]
  refine callLN fh fInternLParam [lEn] [vv fy] internLParamBody [Enc.idxW n] (by decide) rfl (hD fh (by simp)) hcP
    ⟨by simp [sev, vv, Env.get_cons], trivial⟩ (.param n) (internLParam_body_spec ra C hok s n)
    (fun h s' _ => ?_)
  have g2 : ∀ y, y ≠ fh → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fy, Enc.idxW n) :: (fy, Enc.idxW n + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  refine specR_tblSetI hok jL cap st.levels hrel hcap (vv fTL) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide) (by decide)]; exact hTL) i hic h
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- `max a b` / `imax a b` at index `i`. -/
def lvBinP (f : MlS) : ProgHOL 64 :=
  tblFreshP fx (vv fTL) (vv fCap) (vv fI)
    (tblGetP fy (vv fTL) (vv fCap) (vv fU)
      (tblGetP fz (vv fTL) (vv fCap) (vv fV2)
        (.seq (.call (some (some (.local, fh), none)) f [vv fy, vv fz])
          (tblSetP (vv fTL) (vv fI) (vv fh) (.return (.const 0))))))

theorem lvBin_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (f : MlS) (body : ProgHOL 64) (mk : LIdx → LIdx → LNodeView) (rmk : Nat → Nat → LevelRec)
    (hcB : C.code.lookup f = some ([(lEu, .one), (lEv, .one)], body, .one))
    (hbody : ∀ (s : AState) (u v : LIdx),
      SpecR (Pre (σ := σ) C s [(lEu, Enc.idxW u), (lEv, Enc.idxW v)]) body s (internLNode (mk u v)) (PostL C))
    (hred : ∀ (st : StateD) (i a b : Nat) (la lb : LIdx), st.levels.get? i = none →
      st.levels.get? a = some la → st.levels.get? b = some lb →
      parseLevelEntryD st i (rmk a b) =
        (internLNode (mk la lb) >>= fun l => (pure { st with levels := st.levels.insert i l } : AM StateD)))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jL cap : Nat) (hrel : TblRel C.H jL cap st.levels) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTL : Γ.get fTL = some (cellA C jL)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (lvBinP f) s (parseLevelEntryD st i (rmk a b)) (LvPost C jL cap st i) := by
  unfold lvBinP
  refine specR_tblFreshI fx (hD fx (by simp)) jL cap st.levels hrel hcap (vv fTL) (vv fCap) (vv fI)
    (by simpa [sev, vv] using hTL) (by simpa [sev, vv] using hC) i hi (by simpa [sev, vv] using hI)
    (fun hic hg => ?_)
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fy (hD fy (by simp)) jL cap st.levels hrel hcap (vv fTL) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTL)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) a ha
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun la hla => ?_)
  have g2 : ∀ y, y ≠ fy → y ≠ fx →
      Env.get ((fy, Enc.idxW la) :: (fy, Enc.idxW la + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  refine specR_tblGetI fz (hD fz (by simp)) jL cap st.levels hrel hcap (vv fTL) (vv fCap) (vv fV2)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTL)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hC) b hb
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hV) (fun lb hlb => ?_)
  rw [hred st i a b la lb hg hla hlb]
  refine callLN fh f [lEu, lEv] [vv fy, vv fz] body [Enc.idxW la, Enc.idxW lb] (by decide) rfl (hD fh (by simp)) hcB
    ⟨by simp [sev, vv, Env.get_cons, show fy ≠ fz from by decide], by simp [sev, vv, Env.get_cons], trivial⟩ (mk la lb) (hbody s la lb)
    (fun h s' _ => ?_)
  have g3 : ∀ y, y ≠ fh → y ≠ fz → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fz, Enc.idxW lb) :: (fz, Enc.idxW lb + 1) :: (fy, Enc.idxW la) ::
        (fy, Enc.idxW la + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 h4 => by simp only [Env.get_cons, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
  refine specR_tblSetI hok jL cap st.levels hrel hcap (vv fTL) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide) (by decide)]; exact hTL) i hic h
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

theorem lvMax_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcM : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jL cap : Nat) (hrel : TblRel C.H jL cap st.levels) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTL : Γ.get fTL = some (cellA C jL)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (lvBinP fInternLMax) s (parseLevelEntryD st i (.max a b)) (LvPost C jL cap st i) :=
  lvBin_spec ra C hok fInternLMax internLMaxBody LNodeView.max LevelRec.max hcM
    (fun s u v => internLMax_body_spec ra C hok s u v)
    (fun st i a b la lb h1 h2 h3 => by simp [parseLevelEntryD, StateD.freshLevel, StateD.level, IdTable.bound_eq, h1, h2, h3]) s Γ M D hD st jL cap hrel hcap i a b
    hi ha hb hTL hC hI hU hV

theorem lvImax_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcM : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jL cap : Nat) (hrel : TblRel C.H jL cap st.levels) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTL : Γ.get fTL = some (cellA C jL)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (lvBinP fInternLImax) s (parseLevelEntryD st i (.imax a b)) (LvPost C jL cap st i) :=
  lvBin_spec ra C hok fInternLImax internLImaxBody LNodeView.imax LevelRec.imax hcM
    (fun s u v => internLImax_body_spec ra C hok s u v)
    (fun st i a b la lb h1 h2 h3 => by simp [parseLevelEntryD, StateD.freshLevel, StateD.level, IdTable.bound_eq, h1, h2, h3]) s Γ M D hD st jL cap hrel hcap i a b
    hi ha hb hTL hC hI hU hV

end ConPanqueque.Front
