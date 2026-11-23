import ConPanqueque.T.MemoG
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The `defeq` memo: ordered pair of handles ↦ verdict, on the active mode side

Key `[idxW a, idxW b]` in the key buffer, value `boolW v` (so a read returns `0` none, `1` false, `2` true).
-/

namespace ConPanqueque.T

theorem encEE_inj : ∀ x y, encEE x = encEE y → x = y := by
  intro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [encEE, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [Enc.idxW_inj h1, Enc.idxW_inj h2]

/-- The state after the twin's `defeqSet a b v`. -/
def defeqSetS (s : AState) (a b : EIdx) (v : Bool) : AState :=
  { s with caches := { s.caches with defeqC := s.caches.defeqC.insert (a, b) v } }

theorem defeqSet_run (a b : EIdx) (v : Bool) (s : AState) : defeqSet a b v s = .ok ((), defeqSetS s a b v) := rfl

section
variable {σ : Type}

/-- `meo := gEo; KB[0] := ea; KB[1] := eb; x := memoGet(desc defeq, 2); rest`. -/
def defeqGetP (C : Ctx) (x : MlS) (ea eb : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lEo (.var .global gEo))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) ea)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) eb)
        (.seq (.call (some (some (.local, x), none)) fMemoGet [modeD C .defeq, .const 2]) rest)))

/-- `meo := gEo; KB[0] := ea; KB[1] := eb; x := memoSet(desc defeq, 2, ev); rest`. -/
def defeqSetP (C : Ctx) (x : MlS) (ea eb ev : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lEo (.var .global gEo))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) ea)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) eb)
        (.seq (.call (some (some (.local, x), none)) fMemoSet [modeD C .defeq, .const 2, ev]) rest)))

theorem words_kb2 {C : Ctx} {u : PState σ} {a b : EIdx}
    (hM : ∀ x v, (x, v) ∈ [(C.KB + BitVec.ofNat 64 (8 * 0), Enc.idxW a), (C.KB + BitVec.ofNat 64 (8 * 1), Enc.idxW b)] →
      u.memaddrs x ∧ u.memory x = .word v) : Words u C.KB (encEE (a, b)) := by
  intro j hj
  have : j < 2 := by simpa [encEE] using hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact hM _ (Enc.idxW a) (by simp)
  · exact hM _ (Enc.idxW b) (by simp)

/-- The twin's probe of `defeqC` at `(a, b)`, in a caller. -/
theorem specR_defeqGetI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Option Bool → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (ea eb : ExpHOL 64) (a b : EIdx) (hx : x ∈ D) (heo : lEo ∈ D)
    (hea : sev ((lEo, C.eo) :: Γ) ea = some (Enc.idxW a)) (heb : sev ((lEo, C.eo) :: Γ) eb = some (Enc.idxW b))
    (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ r, SpecR (Inv C s ((x, optWG boolW r) :: (lEo, C.eo) :: Γ) [] D) rest s (k r) R) :
    SpecR (Inv C s Γ M D) (defeqGetP C x ea eb rest) s
      ((fun s => .ok (s.caches.defeqC[(a, b)]?, s) : AM (Option Bool)) >>= k) R := by
  refine specR_assignGI lEo gEo C.eo heo (fun u hu => hu.mode.1) ?_
  refine specR_storeKB2I hok ea eb (Enc.idxW a) (Enc.idxW b) hea heb (get_kb_eo hkb) ?_
  exact specR_memoGetGI encEE_inj (C.mG (.m C.side .defeq)) (C.mg (.m C.side .defeq)) s.caches.defeqC (a, b) _ rfl
    (fun u hu => hu.mode.2.1 .defeq) hcodeG hcodeP x (modeD C .defeq) (.const 2) hx (sev_modeD hok _ _) rfl
    (by simp [encEE]) (fun u hM => words_kb2 hM) (hk _)

/-- The twin's `defeqSet a b v`, in a caller. -/
theorem specR_defeqSetI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (ea eb ev : ExpHOL 64) (a b : EIdx) (v : Bool) (hx : x ∈ D) (heo : lEo ∈ D)
    (hea : sev ((lEo, C.eo) :: Γ) ea = some (Enc.idxW a)) (heb : sev ((lEo, C.eo) :: Γ) eb = some (Enc.idxW b))
    (hev : sev ((lEo, C.eo) :: Γ) ev = some (boolW v)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv C (defeqSetS s a b v) ((x, w) :: (lEo, C.eo) :: Γ) [] D) rest (defeqSetS s a b v) (k ()) R) :
    SpecR (Inv C s Γ M D) (defeqSetP C x ea eb ev rest) s (defeqSet a b v >>= k) R := by
  refine specR_assignGI lEo gEo C.eo heo (fun u hu => hu.mode.1) ?_
  refine specR_storeKB2I hok ea eb (Enc.idxW a) (Enc.idxW b) hea heb (get_kb_eo hkb) ?_
  refine specR_memoSetGI encEE_inj (C.mG (.m C.side .defeq)) (C.mg (.m C.side .defeq)) s.caches.defeqC (a, b) v _
    (defeqSet_run a b v s) (fun u hu => hu.mode.2.1 .defeq)
    (fun i hi => hok.kbMemo _ i (by simp [encEE] at hi; omega)) (fun j hj => hok.mdescMemo _ _ j hj)
    (fun u u' hsr hmem hfr hd hg hc => ?_) hcodeS hcodeI x (modeD C .defeq) (.const 2) ev hx (sev_modeD hok _ _) rfl hev
    (by simp [encEE]) (fun u hM => words_kb2 hM) hk
  refine sr_upd_mode hok .defeq hsr hfr hd hg hc rfl rfl rfl ⟨rfl, rfl, rfl⟩ ?_
  exact modeAt_setG hok hsr.mode .defeq hmem (fun k' hk' => by cases k' <;> first | rfl | exact absurd rfl hk')
    rfl hfr hd (by rw [hg])

end

end ConPanqueque.T
