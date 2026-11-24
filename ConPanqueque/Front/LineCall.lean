import ConPanqueque.Front.FrontSt

/-! # Calling a line function

A line procedure becomes a function: the uniform parameters `linePs`, its locals zeroed and the
context loaded by `prologue`.  `specR_lineCall` is the call rule: the callee's core runs in the
`Inv` world at the parameters' values, and the caller continues at the image the post names. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ExprRec LevelRec NameRec)

variable {σ : Type}

/-- The line functions' parameters. -/
def linePs : List MlS := [fTN, fTL, fTE, fCap, fI, fU, kPos, kBA, kBN, kRB, kCapD]

theorem linePs_nodup : linePs.Nodup := by decide

theorem env_zip_get {u : PState σ} : ∀ (ps : List MlS) (vs : List (BitVec 64)) (hl : vs.length = ps.length),
    (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
    ∀ x v, Env.get (ps.zip vs) x = some v → u.locals.lookup x = some (.val (.word v))
  | [], [], _, _, x, v, h => by simp [Env.get] at h
  | p :: ps, w :: vs, hl, hall, x, v, h => by
    simp only [List.zip_cons_cons, Env.get] at h
    split at h
    · rename_i e; subst e; simp only [Option.some.injEq] at h; subst h
      exact hall 0 (by simp)
    · exact env_zip_get ps vs (by simpa using hl) (fun i hi => hall (i + 1) (by simp; omega)) x v h
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl

/-- The call rule for a function `prologue L core` with word parameters `ps`. -/
theorem specR_protoCall {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (hnd : ps.Nodup) (L : List MlS) (core : ProgHOL 64) (es : List (ExpHOL 64))
    (vs : List (BitVec 64)) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), prologue L core, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hL : ∀ y, y ∈ L → Env.get (ctxEnv C ++ ps.zip vs) y = none)
    (Rf : α → BitVec 64 → AState → PState σ → Prop)
    (hRl : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)), Rf a w s' st →
      Rf a w s' { st with locals := L })
    (hcore : SpecR (Inv C s (ctxEnv C ++ ps.zip vs) [] (ctxLocals ++ L)) core s m Rf)
    (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hk : ∀ a w s' H', Qx a w s' H' → SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIA x f ps es (prologue L core) vs hnd hl hx hC hes Rf Qx hRf
    (fun u hu _ hlk t ht => by
      subst ht
      exact specR_prologue hRl hL hcore t ⟨hu, env_zip_get ps vs hl hlk⟩)
    hk

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

/-- An expression line's call: the caller continues at `FrontSt` of the new image. -/
theorem specR_exLineCall {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : StateD → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (L : List MlS) (core : ProgHOL 64) (es : List (ExpHOL 64)) (vs : List (BitVec 64))
    (hl : vs.length = linePs.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue L core, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hL : ∀ y, y ∈ L → Env.get (ctxEnv C ++ linePs.zip vs) y = none)
    (st : StateD) (i : Nat) (r : ExprRec) (hi : i < cap) (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (hcore : SpecR (Inv (σ := σ) C s (ctxEnv C ++ linePs.zip vs) [] (ctxLocals ++ L)) core s (parseExprEntryD st i r)
      (ExPost C jE cap st i))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k st') R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s
      (parseExprEntryD st i r >>= k) R :=
  specR_protoCall x f linePs linePs_nodup L core es vs hl hx hC hes hL _
    (fun _ _ _ _ _ ⟨w', h1, h2⟩ => ⟨w', sr_of_eq h1 rfl rfl rfl rfl, h2⟩) hcore
    (fun st' _ _ H' => FrontSt C F rb capD jN jL jE cap bufJ b H' st')
    (fun st' w s' t' ⟨w', hsr, hE, h1, h2, h3⟩ => ⟨_, frontSt_setE hfs i hi w' hE h1 h2 h3, hsr⟩) hk

theorem specR_lvLineCall {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : StateD → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (L : List MlS) (core : ProgHOL 64) (es : List (ExpHOL 64)) (vs : List (BitVec 64))
    (hl : vs.length = linePs.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue L core, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hL : ∀ y, y ∈ L → Env.get (ctxEnv C ++ linePs.zip vs) y = none)
    (st : StateD) (i : Nat) (r : LevelRec) (hi : i < cap) (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (hcore : SpecR (Inv (σ := σ) C s (ctxEnv C ++ linePs.zip vs) [] (ctxLocals ++ L)) core s (parseLevelEntryD st i r)
      (LvPost C jL cap st i))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k st') R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s
      (parseLevelEntryD st i r >>= k) R :=
  specR_protoCall x f linePs linePs_nodup L core es vs hl hx hC hes hL _
    (fun _ _ _ _ _ ⟨w', h1, h2⟩ => ⟨w', sr_of_eq h1 rfl rfl rfl rfl, h2⟩) hcore
    (fun st' _ _ H' => FrontSt C F rb capD jN jL jE cap bufJ b H' st')
    (fun st' w s' t' ⟨w', hsr, hL', h1, h2, h3⟩ => ⟨_, frontSt_setL hfs i hi w' hL' h1 h2 h3, hsr⟩) hk

theorem specR_nmLineCall {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : StateD → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (L : List MlS) (core : ProgHOL 64) (es : List (ExpHOL 64)) (vs : List (BitVec 64))
    (hl : vs.length = linePs.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue L core, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hL : ∀ y, y ∈ L → Env.get (ctxEnv C ++ linePs.zip vs) y = none)
    (st : StateD) (i : Nat) (r : NameRec) (hi : i < cap) (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (hcore : SpecR (Inv (σ := σ) C s (ctxEnv C ++ linePs.zip vs) [] (ctxLocals ++ L)) core s (parseNameEntryD st i r)
      (NmPost C jN cap st i))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k st') R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s
      (parseNameEntryD st i r >>= k) R :=
  specR_protoCall x f linePs linePs_nodup L core es vs hl hx hC hes hL _
    (fun _ _ _ _ _ ⟨w', h1, h2⟩ => ⟨w', sr_of_eq h1 rfl rfl rfl rfl, h2⟩) hcore
    (fun st' _ _ H' => FrontSt C F rb capD jN jL jE cap bufJ b H' st')
    (fun st' w s' t' ⟨w', hsr, hN, h1, h2, h3⟩ => ⟨_, frontSt_setN hfs i hi w' hN h1 h2 h3, hsr⟩) hk

theorem specR_dcLineCall {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (L : List MlS) (core : ProgHOL 64) (es : List (ExpHOL 64)) (vs : List (BitVec 64))
    (hl : vs.length = linePs.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue L core, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hL : ∀ y, y ∈ L → Env.get (ctxEnv C ++ linePs.zip vs) y = none)
    (st : StateD) (d : ConLeche.Frontend.DeclRec) (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (hcore : SpecR (Inv (σ := σ) C s (ctxEnv C ++ linePs.zip vs) [] (ctxLocals ++ L)) core s (processLineCoreD st d)
      (fun a w s' t' => ∃ dd, DeclPost C F rb capD C.H st dd a w s' t'))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s
      (processLineCoreD st d >>= k) R :=
  specR_protoCall x f linePs linePs_nodup L core es vs hl hx hC hes hL _
    (fun _ _ _ _ _ ⟨dd, ha, H', h1, h2⟩ => ⟨dd, ha, H', sr_of_eq h1 rfl rfl rfl rfl, h2⟩) hcore
    (fun a _ _ H' => ∃ st', a = .inl st' ∧ FrontSt C F rb capD jN jL jE cap bufJ b H' st')
    (fun a w s' t' ⟨dd, ha, H', hsr, hag, hlen, hdr⟩ =>
      ⟨H', ⟨_, ha, frontSt_decl hfs dd hag hlen hdr⟩, hsr⟩)
    (fun a w s' H' ⟨st', ha, hf⟩ => by subst ha; exact hk st' w s' H' hf)

end

end ConPanqueque.Front
