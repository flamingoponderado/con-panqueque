import ConPanqueque.Front.Level
import ConPanqueque.T.EIntern2

/-! # Expression records into the store (`parseExprEntryD`)

As for levels: the freshness test, the table reads in the twin's order, the ported intern
procedure, the table write.  Here: `bvar`, `sort`, `app`, `lam`, `forallE`, `letE`, `proj`.
(`const` needs its level list interned first; `natVal` and `strVal` need the literal's bytes.) -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable ExprRec)

variable {σ : Type}

def fTE := ofString "fte"
def fW3 := ofString "fw"

/-- After an expression record: the store represented with the expression table's cell written, the
rest of the parse state as it was. -/
def ExPost (C : Ctx) (jE cap : Nat) (st : StateD) (i : Nat) :
    StateD → BitVec 64 → AState → PState σ → Prop :=
  fun st' _ s' t' => ∃ w', SR (ctxH C (C.H.set (jE + i) w')) s' t' ∧
    TblRel (C.H.set (jE + i) w') jE cap st'.exprs ∧
    st'.names = st.names ∧ st'.levels = st.levels ∧ st'.decls = st.decls

/-- An expression-building call whose callee is specified by `PostE` (the handle and the new state). -/
theorem callEN {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM EIdx} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s m (PostE C))
    (hk : ∀ h s', m s = .ok (h, s') → SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIM x f ps es B vs hnd hl hx hC hes
    (fun a w s' st => m s = .ok (a, s') ∧ PostE C a w s' st) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ hlk => specR_run (fun w hw => by subst hw; exact hspec _ (pre_of_lookups hu ps vs hl hlk)))
    (fun h w s' st ⟨hr, hw, _⟩ => by subst hw; exact hk h s' hr)

theorem specR_exFresh {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hD : fx ∈ D) (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i : Nat) (hi : i < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i))
    (hk : i < cap → st.exprs.get? i = none → SpecR (Inv C s ((fx, 0) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (tblFreshP fx (vv fTE) (vv fCap) (vv fI) rest) s m R :=
  specR_tblFreshI fx hD jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fI)
    (by simpa [sev, vv] using hTE) (by simpa [sev, vv] using hC) i hi (by simpa [sev, vv] using hI) hk

/-- `bvar k` at index `i`. -/
def exBVarP : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (.seq (.call (some (some (.local, fh), none)) fInternBVar [vv fU])
      (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0))))

theorem exBVar_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcB : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i k : Nat) (hi : i < 2 ^ 64) (hk : k < 2 ^ 63)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 k)) :
    SpecR (Inv (σ := σ) C s Γ M D) exBVarP s (parseExprEntryD st i (.bvar k)) (ExPost C jE cap st i) := by
  unfold exBVarP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi hTE hC hI (fun hic hg => ?_)
  have hm : parseExprEntryD st i (.bvar k) =
      (internBVarE k >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, IdTable.bound_eq, hg, internBVarE]
  rw [hm]
  refine specR_internBVarI ra hok hcB fh (vv fU) k hk (hD fh (by simp))
    (by simp only [sev, vv]; rw [Env.get_cons, if_neg (by decide)]; exact hU) (fun h s' => ?_)
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv, Env.get_cons, if_neg (show fTE ≠ fh by decide), if_neg (show fTE ≠ fx by decide)]
        exact hTE) i hic h
    (by simp only [sev, vv, Env.get_cons, if_neg (show fI ≠ fh by decide), if_neg (show fI ≠ fx by decide)]
        exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- `sort u` at index `i` (the level from the level table). -/
def exSortP : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (tblGetP fy (vv fTL) (vv fCap) (vv fU)
      (.seq (.call (some (some (.local, fh), none)) fInternSort [vv fy])
        (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0)))))

theorem exSort_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fh], x ∈ D)
    (st : StateD) (jE jL cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hrell : TblRel C.H jL cap st.levels)
    (hcap : 8 * cap < 2 ^ 64) (i u : Nat) (hi : i < 2 ^ 64) (hu : u < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hTL : Γ.get fTL = some (cellA C jL))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 u)) :
    SpecR (Inv (σ := σ) C s Γ M D) exSortP s (parseExprEntryD st i (.sort u)) (ExPost C jE cap st i) := by
  unfold exSortP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi hTE hC hI (fun hic hg => ?_)
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  refine specR_tblGetI fy (hD fy (by simp)) jL cap st.levels hrell hcap (vv fTL) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTL)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) u hu
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun lu hlu => ?_)
  have hm : parseExprEntryD st i (.sort u) =
      (internSortE lu >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, StateD.level, IdTable.bound_eq, hg, hlu, internSortE]
  rw [hm]
  refine callEN fh fInternSort [lEu] [vv fy] sortBody [Enc.idxW lu] (by decide) rfl (hD fh (by simp)) hcS
    ⟨by simp [sev, vv, Env.get_cons], trivial⟩ (sort_body_spec ra C hok s lu) (fun h s' _ => ?_)
  have g2 : ∀ y, y ≠ fh → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fy, Enc.idxW lu) :: (fy, Enc.idxW lu + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide) (by decide)]; exact hTE) i hic h
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- A two-child expression (`app`, `lam`, `forallE`) at index `i`. -/
def exBinP (f : MlS) : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (tblGetP fy (vv fTE) (vv fCap) (vv fU)
      (tblGetP fz (vv fTE) (vv fCap) (vv fV2)
        (.seq (.call (some (some (.local, fh), none)) f [vv fy, vv fz])
          (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0))))))

theorem exBin_spec (C : Ctx) (hok : CtxOK C) (f : MlS) (op : EIdx → EIdx → AM EIdx) (rmk : Nat → Nat → ExprRec)
    (hI2 : ∀ (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (rest : ProgHOL 64) (k : EIdx → AM StateD)
      (R : StateD → BitVec 64 → AState → PState σ → Prop) (x : MlS) (e1 e2 : ExpHOL 64) (a b : EIdx), x ∈ D →
      sev Γ e1 = some (Enc.idxW a) → sev Γ e2 = some (Enc.idxW b) →
      (∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) →
      SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2]) rest) s (op a b >>= k) R)
    (hred : ∀ (st : StateD) (i a b : Nat) (ea eb : EIdx), st.exprs.get? i = none →
      st.exprs.get? a = some ea → st.exprs.get? b = some eb →
      parseExprEntryD st i (rmk a b) =
        (op ea eb >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD)))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (exBinP f) s (parseExprEntryD st i (rmk a b)) (ExPost C jE cap st i) := by
  unfold exBinP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi hTE hC hI (fun hic hg => ?_)
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  refine specR_tblGetI fy (hD fy (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) a ha
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun ea hea => ?_)
  have g2 : ∀ y, y ≠ fy → y ≠ fx →
      Env.get ((fy, Enc.idxW ea) :: (fy, Enc.idxW ea + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, if_neg h1, if_neg h2]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fV2)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hC) b hb
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hV) (fun eb heb => ?_)
  rw [hred st i a b ea eb hg hea heb]
  refine hI2 s _ M D _ _ _ fh (vv fy) (vv fz) ea eb (hD fh (by simp))
    (by simp [sev, vv, Env.get_cons, show fy ≠ fz from by decide]) (by simp [sev, vv, Env.get_cons])
    (fun h s' => ?_)
  have g3 : ∀ y, y ≠ fh → y ≠ fz → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fz, Enc.idxW eb) :: (fz, Enc.idxW eb + 1) :: (fy, Enc.idxW ea) ::
        (fy, Enc.idxW ea + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 h4 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide) (by decide)]; exact hTE) i hic h
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

theorem exApp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (exBinP fInternApp) s (parseExprEntryD st i (.app a b)) (ExPost C jE cap st i) :=
  exBin_spec C hok fInternApp internAppE ExprRec.app
    (fun s Γ M D rest k R x e1 e2 a b hx h1 h2 hk => specR_internAppI ra hok hcA x e1 e2 a b hx h1 h2 hk)
    (fun st i a b ea eb h1 h2 h3 => by
      simp [parseExprEntryD, StateD.freshExpr, StateD.expr, IdTable.bound_eq, h1, h2, h3, internAppE])
    s Γ M D hD st jE cap hrel hcap i a b hi ha hb hTE hC hI hU hV

theorem exLam_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcL : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (exBinP fInternLam) s (parseExprEntryD st i (.lam a b)) (ExPost C jE cap st i) :=
  exBin_spec C hok fInternLam internLamE ExprRec.lam
    (fun s Γ M D rest k R x e1 e2 a b hx h1 h2 hk => specR_internLamI ra hok hcL x e1 e2 a b hx h1 h2 hk)
    (fun st i a b ea eb h1 h2 h3 => by
      simp [parseExprEntryD, StateD.freshExpr, StateD.expr, IdTable.bound_eq, h1, h2, h3, internE])
    s Γ M D hD st jE cap hrel hcap i a b hi ha hb hTE hC hI hU hV

theorem exForall_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcF : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i a b : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) :
    SpecR (Inv (σ := σ) C s Γ M D) (exBinP fInternForallE) s (parseExprEntryD st i (.forallE a b))
      (ExPost C jE cap st i) :=
  exBin_spec C hok fInternForallE internForallEE ExprRec.forallE
    (fun s Γ M D rest k R x e1 e2 a b hx h1 h2 hk => specR_internForallEI ra hok hcF x e1 e2 a b hx h1 h2 hk)
    (fun st i a b ea eb h1 h2 h3 => by
      simp [parseExprEntryD, StateD.freshExpr, StateD.expr, IdTable.bound_eq, h1, h2, h3, internE])
    s Γ M D hD st jE cap hrel hcap i a b hi ha hb hTE hC hI hU hV

/-- `letE ty vl bd` at index `i`. -/
def exLetP : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (tblGetP fy (vv fTE) (vv fCap) (vv fU)
      (tblGetP fz (vv fTE) (vv fCap) (vv fV2)
        (tblGetP fW3 (vv fTE) (vv fCap) (vv fTN)
          (.seq (.call (some (some (.local, fh), none)) fInternLet [vv fy, vv fz, vv fW3])
            (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0)))))))

/-- The third child's index is passed in `fTN` (the let record has no name). -/
theorem exLet_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcL : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fW3, fh], x ∈ D)
    (st : StateD) (jE cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (i a b c : Nat) (hi : i < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 a))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 b)) (hW : Γ.get fTN = some (BitVec.ofNat 64 c)) :
    SpecR (Inv (σ := σ) C s Γ M D) exLetP s (parseExprEntryD st i (.letE a b c)) (ExPost C jE cap st i) := by
  unfold exLetP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi hTE hC hI (fun hic hg => ?_)
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  refine specR_tblGetI fy (hD fy (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) a ha
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun ea hea => ?_)
  have g2 : ∀ y, y ≠ fy → y ≠ fx →
      Env.get ((fy, Enc.idxW ea) :: (fy, Enc.idxW ea + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, if_neg h1, if_neg h2]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fV2)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hC) b hb
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hV) (fun eb heb => ?_)
  have g3 : ∀ y, y ≠ fz → y ≠ fy → y ≠ fx →
      Env.get ((fz, Enc.idxW eb) :: (fz, Enc.idxW eb + 1) :: (fy, Enc.idxW ea) :: (fy, Enc.idxW ea + 1) ::
        (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
  refine specR_tblGetI fW3 (hD fW3 (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fTN)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hC) c hc
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hW) (fun ec hec => ?_)
  have hm : parseExprEntryD st i (.letE a b c) =
      (internLetEE ea eb ec >>= fun e => (pure { st with exprs := st.exprs.insert i e } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, StateD.expr, IdTable.bound_eq, hg, hea, heb, hec, internLetEE]
  rw [hm]
  refine specR_internLetI ra hok hcL fh (vv fy) (vv fz) (vv fW3) ea eb ec (hD fh (by simp))
    (by simp [sev, vv, Env.get_cons, show fy ≠ fz from by decide, show fy ≠ fW3 from by decide])
    (by simp [sev, vv, Env.get_cons, show fz ≠ fW3 from by decide]) (by simp [sev, vv, Env.get_cons])
    (fun h s' => ?_)
  have g4 : ∀ y, y ≠ fh → y ≠ fW3 → y ≠ fz → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fW3, Enc.idxW ec) :: (fW3, Enc.idxW ec + 1) :: (fz, Enc.idxW eb) ::
        (fz, Enc.idxW eb + 1) :: (fy, Enc.idxW ea) :: (fy, Enc.idxW ea + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 h4 h5 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTE) i hic h
    (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

/-- `proj tn ix s` at index `i`: the type name from the name table, the structure from the expression
table, the field index as a word (`fV2`); the struct's index in `fU`, the name's in `fTN`... -/
def exProjP : ProgHOL 64 :=
  tblFreshP fx (vv fTE) (vv fCap) (vv fI)
    (tblGetP fy (vv fTN) (vv fCap) (vv fU)
      (tblGetP fz (vv fTE) (vv fCap) (vv fW3)
        (.seq (.call (some (some (.local, fh), none)) fInternProj [vv fy, vv fz, vv fV2])
          (tblSetP (vv fTE) (vv fI) (vv fh) (.return (.const 0))))))

theorem exProj_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [fx, fy, fz, fh], x ∈ D)
    (st : StateD) (jE jN cap : Nat) (hrel : TblRel C.H jE cap st.exprs) (hreln : TblRel C.H jN cap st.names)
    (hcap : 8 * cap < 2 ^ 64) (i tn ix e : Nat) (hi : i < 2 ^ 64) (htn : tn < 2 ^ 64) (hix : ix < 2 ^ 63)
    (he : e < 2 ^ 64) (jNA : BitVec 64)
    (hTE : Γ.get fTE = some (cellA C jE)) (hTN : Γ.get fTN = some (cellA C jN))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hI : Γ.get fI = some (BitVec.ofNat 64 i)) (hU : Γ.get fU = some (BitVec.ofNat 64 tn))
    (hV : Γ.get fV2 = some (BitVec.ofNat 64 ix)) (hW : Γ.get fW3 = some (BitVec.ofNat 64 e)) :
    SpecR (Inv (σ := σ) C s Γ M D) exProjP s (parseExprEntryD st i (.proj tn ix e)) (ExPost C jE cap st i) := by
  unfold exProjP
  refine specR_exFresh (hD fx (by simp)) st jE cap hrel hcap i hi hTE hC hI (fun hic hg => ?_)
  have g1 : ∀ y, y ≠ fx → Env.get ((fx, 0) :: Γ) y = Env.get Γ y := fun y h => by rw [Env.get_cons, if_neg h]
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTN)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC) tn htn
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hU) (fun n hn => ?_)
  have g2 : ∀ y, y ≠ fy → y ≠ fx →
      Env.get ((fy, Enc.idxW n) :: (fy, Enc.idxW n + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 => by simp only [Env.get_cons, if_neg h1, if_neg h2]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrel hcap (vv fTE) (vv fCap) (vv fW3)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hC) e he
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hW) (fun ee hee => ?_)
  have hm : parseExprEntryD st i (.proj tn ix e) =
      (internProjE n ix ee >>= fun x => (pure { st with exprs := st.exprs.insert i x } : AM StateD)) := by
    simp [parseExprEntryD, StateD.freshExpr, StateD.expr, StateD.name, IdTable.bound_eq, hg, hn, hee, internProjE]
  rw [hm]
  have g3 : ∀ y, y ≠ fz → y ≠ fy → y ≠ fx →
      Env.get ((fz, Enc.idxW ee) :: (fz, Enc.idxW ee + 1) :: (fy, Enc.idxW n) :: (fy, Enc.idxW n + 1) ::
        (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3]
  refine specR_internProjI ra hok hcP fh (vv fy) (vv fz) (vv fV2) n ix ee hix (hD fh (by simp))
    (by simp [sev, vv, Env.get_cons, show fy ≠ fz from by decide]) (by simp [sev, vv, Env.get_cons])
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hV)
    (fun h s' => ?_)
  have g4 : ∀ y, y ≠ fh → y ≠ fz → y ≠ fy → y ≠ fx →
      Env.get ((fh, Enc.idxW h) :: (fz, Enc.idxW ee) :: (fz, Enc.idxW ee + 1) :: (fy, Enc.idxW n) ::
        (fy, Enc.idxW n + 1) :: (fx, 0) :: Γ) y = Env.get Γ y :=
    fun y h1 h2 h3 h4 => by simp only [Env.get_cons, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  refine specR_tblSetI hok jE cap st.exprs hrel hcap (vv fTE) (vv fI) (vv fh)
    (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hTE) i hic h
    (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hI)
    (by simp [sev, vv, Env.get_cons]) (fun hrel' => ?_)
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨_, sr_of_eq ht.sr rfl rfl rfl rfl, hrel', rfl, rfl, rfl⟩)

end ConPanqueque.Front
