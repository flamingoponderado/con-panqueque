import ConPanqueque.T.Decl.LevelParams
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `allLevelParamsDefined`: the memoized walk

The DAG walk with a handle-keyed memo (a memo list keyed `(handle, 0)`, as `constsResolveF`'s), the memo
consulted first at every node; leaves `sort` / `const` run the level side (`lpd` / `lpa`) against the parameter
block. The walk reuses `constsResolveF`'s locals, so its pair-block return and memo insertion are those.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def alP := ofString "al_p"
def alN := ofString "al_n"
def fAl := ofString "allLevelParamsDefinedGo"

def alParams : List MlS := [crfF, crfH, crfM, alP, alN]

/-- One recursive call; its answer and memo read back. -/
def alCall (k : MlS) (eH eM : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fAl [.op .sub [vv crfF, .const 1], eH, eM, vv alP, vv alN])
  (.seq (.assign .local crfR (.load .one (vv k))) (.seq (.assign .local crfM2 (.load .one (.op .add [vv k, .const 8])))
    rest))

def alArm1 (C : Ctx) : ProgHOL 64 := alCall crfK1 (vv crfC1) (vv crfM) (crfIns C)

def alArm2 (C : Ctx) : ProgHOL 64 :=
  alCall crfK1 (vv crfC1) (vv crfM) (.ite (vv crfR) (alCall crfK2 (vv crfC2) (vv crfM2) (crfIns C)) (crfIns C))

def alArm3 (C : Ctx) : ProgHOL 64 :=
  alCall crfK1 (vv crfC1) (vv crfM) (.ite (vv crfR)
    (alCall crfK2 (vv crfC2) (vv crfM2) (.ite (vv crfR) (alCall crfK3 (vv crfC3) (vv crfM2) (crfIns C)) (crfIns C)))
    (crfIns C))

def alCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv crfF) (.const 0)) hang
  (.seq (.call (some (some (.local, crfL), none)) fMl [vv crfM, vv crfH, .const 0])
  (.ite (.cmp .notEqual (vv crfL) (.const 0)) (crfRet C (.op .sub [vv crfL, .const 1]) (vv crfM))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv crfH)) (.seq eViewP
  (.ite (.op .or [.cmp .equal (vv lDg) (.const 0), .cmp .equal (vv lDg) (.const 8)])
    (.seq (.assign .local crfR (.const 1)) (.seq (.assign .local crfM2 (vv crfM)) (crfIns C)))
  (.ite (.cmp .equal (vv lDg) (.const 2))
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, crfR), none)) fLpd [vv crfC1, vv alP, vv alN])
    (.seq (.assign .local crfM2 (vv crfM)) (crfIns C))))
  (.ite (.cmp .equal (vv lDg) (.const 3))
    (.seq (.assign .local crfC1 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv crfC1)) (.seq lsViewP
    (.seq (.call (some (some (.local, crfR), none)) fLpa [vv crfC1, vv alP, vv alN, .const 0])
    (.seq (.assign .local crfM2 (vv crfM)) (crfIns C)))))))
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.assign .local crfC1 (.load .one (vv lRp))) (alArm1 C))
  (.ite (.op .or [.op .or [.cmp .equal (vv lDg) (.const 4), .cmp .equal (vv lDg) (.const 5)], .cmp .equal (vv lDg) (.const 6)])
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
      (.seq (.assign .local crfC2 (.load .one (.op .add [vv lRp, .const 8]))) (alArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local crfC1 (.load .one (vv lRp)))
      (.seq (.assign .local crfC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local crfC3 (.load .one (.op .add [vv lRp, .const 16]))) (alArm3 C))))
    (.seq (.assign .local crfC1 (.load .one (.op .add [vv lRp, .const 8]))) (alArm1 C)))))))))))))

def alBody (C : Ctx) : ProgHOL 64 := prologue crfLocals (alCore C)

structure AlCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  self : C.code.lookup fAl = some (alParams.map (fun p => (p, ShapeHOL.one)), alBody C, .one)
  lp : LpCodes C

section
variable {σ : Type}

theorem al_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crfLocals → (ctxEnv C ++ alParams.zip vals).get x = none :=
  Knot.params_none C crfLocals alParams vals (by decide) (by decide)

/-- `PostCr`, the state unchanged (the walk is read-only on the twin side). -/
def PostAl (C : Ctx) (s0 : AState) (rm : Bool × Std.HashMap EIdx Bool) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  PostCr C rm w s' st ∧ s' = s0

theorem postAl_locals (C : Ctx) (s0 : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostAl C s0 a w s' st → PostAl C s0 a w s' { st with locals := L } :=
  fun a w s' st L ⟨h1, h2⟩ => ⟨postCr_locals C a w s' st L h1, h2⟩

/-- A `pure` twin leaves the state as it was. -/
theorem specR_pureState {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {a : α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR P c s (pure a) R) :
    SpecR P c s (pure a) (fun a' w s' st => R a' w s' st ∧ s' = s) := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a', s', hm, hq⟩
  · exact Or.inl hs
  · refine Or.inr ⟨w, hr, a', s', hm, hq, ?_⟩
    have : (Except.ok (a, s) : Except _ _) = .ok (a', s') := hm
    cases this; rfl

theorem specR_alRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (er em : ExpHOL 64) (r : Bool) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : crfO ∈ D) (her : ∀ w, sev ((crfO, w) :: Γ) er = some (boolW r)) (hem : ∀ w, sev ((crfO, w) :: Γ) em = some pm)
    (hrep : CrRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfRet C er em) s (pure (r, memo)) (PostAl (ctxH C H0) s) :=
  specR_pureState (specR_crfRetI hok er em r pm memo hD her hem hrep h0)

theorem specR_alInsI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (h : EIdx) (r : Bool) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool) (hD : crfN ∈ D ∧ crfO ∈ D) (hH : Γ.get crfH = some (Enc.idxW h))
    (hR : Γ.get crfR = some (boolW r)) (hM : Γ.get crfM2 = some pm)
    (hrep : CrRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (crfIns C) s (pure (r, memo.insert h r)) (PostAl (ctxH C H0) s) :=
  specR_pureState (specR_crfInsI hok h r pm memo hD hH hR hM hrep h0)

/-- The walk's spec at fuel `n`, for every argument. -/
def AlRec (C : Ctx) (o : Nat) (xs : List NIdx) (ks : List ConLeche.Name) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx Bool) (H : List (BitVec 64)) (s : AState) (pm : BitVec 64),
    C.H <+: H → CrRep C H pm memo → LpsAt C s o xs ks →
    SpecR (σ := σ) (Pre (ctxH C H) s (alParams.zip [BitVec.ofNat 64 n, Enc.idxW h, pm, cellA C o,
      BitVec.ofNat 64 xs.length])) (alBody C) s (allLevelParamsDefinedGo ks memo n h) (PostAl (ctxH C H) s)

/-- One recursive call, then the pair block read back. -/
theorem specR_alCallI {α : Type} {C : Ctx} (hc : AlCodes C) {o : Nat} {xs : List NIdx} {ks : List ConLeche.Name}
    {n : Nat} (ih : AlRec (σ := σ) C o xs ks n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool × Std.HashMap EIdx Bool → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eH eM : ExpHOL 64) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hx : x ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D) (hxn : x ≠ crfR ∧ crfM2 ≠ x) (hp : C.H <+: H) (hrep : CrRep C H pm memo)
    (hL : LpsAt C s o xs ks)
    (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1))) (hP : Γ.get alP = some (cellA C o))
    (hN : Γ.get alN = some (BitVec.ofNat 64 xs.length))
    (heH : sev Γ eH = some (Enc.idxW h)) (heM : sev Γ eM = some pm)
    (hk : ∀ (rm : Bool × Std.HashMap EIdx Bool) H' pm' w, H <+: H' → CrRep C H' pm' rm.2 →
      SpecR (Inv (ctxH C H') s ((crfM2, pm') :: (crfR, boolW rm.1) :: (x, w) :: Γ) [] D) rest s (k rm) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (alCall x eH eM rest) s (allLevelParamsDefinedGo ks memo n h >>= k) R := by
  unfold alCall
  refine specR_callNIH (C := ctxH C H) x fAl alParams [.op .sub [vv crfF, .const 1], eH, eM, vv alP, vv alN] (alBody C)
    [BitVec.ofNat 64 n, Enc.idxW h, pm, cellA C o, BitVec.ofNat 64 xs.length] (by decide) rfl hx.1 hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, heH, heM, by simp [sev, hP], by simp [sev, hN], trivial⟩
    (PostAl (ctxH C H) s)
    (fun rm w s' H' => s' = s ∧ ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      CrRep C H' pm' rm.2)
    (fun rm w s' st ⟨⟨H', o, pm', hp', hw, h0, h1', hrep', hsr⟩, hs⟩ =>
      ⟨H', hp', ⟨hs, o, pm', hw, h0, h1', crRep_ofH hrep'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu alParams _ rfl hlk) (ih h memo H s pm hp hrep hL))
    (fun rm w s' H' hp' ⟨hs, o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst hw hs
  refine UD.specR_heapLoadI' (C := ctxH C H') crfR (vv x) o (boolW rm.1) h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') crfM2 (.op .add [vv x, .const 8]) (o + 1) pm' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk rm H' pm' (cellA C o) hp' hrep'


abbrev ALM := Std.HashMap EIdx Bool

theorem specR_alArm1I {C : Ctx} (hok : CtxOK C) (hc : AlCodes C) {o : Nat} {xs : List NIdx}
    {ks : List ConLeche.Name} {n : Nat} (ih : AlRec (σ := σ) C o xs ks n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 : EIdx) (pm : BitVec 64)
    (memo : ALM) (hD : crfK1 ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hL : LpsAt C s o xs ks)
    (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1))) (hP : Γ.get alP = some (cellA C o))
    (hN : Γ.get alN = some (BitVec.ofNat 64 xs.length))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm) (hC1 : Γ.get crfC1 = some (Enc.idxW c1)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (alArm1 C) s
      (allLevelParamsDefinedGo ks memo n c1 >>= fun p => pure (p.1, p.2.insert h p.1)) (PostAl (ctxH C H0) s) := by
  unfold alArm1
  refine specR_alCallI hc ih crfK1 (vv crfC1) (vv crfM) c1 pm memo ⟨hD.1, hD.2.1, hD.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hL hF hP hN (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  exact specR_alInsI hok h rm.1 pm1 rm.2 ⟨hD.2.2.2.1, hD.2.2.2.2⟩ (by simp +decide [Env.get, hH])
    (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep1 (h0.trans hp1)

theorem specR_alArm2I {C : Ctx} (hok : CtxOK C) (hc : AlCodes C) {o : Nat} {xs : List NIdx}
    {ks : List ConLeche.Name} {n : Nat} (ih : AlRec (σ := σ) C o xs ks n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 c2 : EIdx) (pm : BitVec 64)
    (memo : ALM) (K : Bool × ALM → AM (Bool × ALM)) (hKf : ∀ m, K (false, m) = pure (false, m) >>= (fun y => pure (y.1, y.2.insert h y.1)))
    (hKt : ∀ m, K (true, m) = allLevelParamsDefinedGo ks m n c2 >>= (fun y => pure (y.1, y.2.insert h y.1)))
    (hD : crfK1 ∈ D ∧ crfK2 ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hL : LpsAt C s o xs ks)
    (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1))) (hP : Γ.get alP = some (cellA C o))
    (hN : Γ.get alN = some (BitVec.ofNat 64 xs.length))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm) (hC1 : Γ.get crfC1 = some (Enc.idxW c1))
    (hC2 : Γ.get crfC2 = some (Enc.idxW c2)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (alArm2 C) s (allLevelParamsDefinedGo ks memo n c1 >>= K)
      (PostAl (ctxH C H0) s) := by
  unfold alArm2
  refine specR_alCallI hc ih crfK1 (vv crfC1) (vv crfM) c1 pm memo ⟨hD.1, hD.2.2.1, hD.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hL hF hP hN (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨b1, m1⟩ := rm
  cases b1
  · simp only [hKf, pure_bind]
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_alInsI hok h false pm1 m1 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
      (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep1 (h0.trans hp1)
  · simp only [hKt]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_alCallI hc ih crfK2 (vv crfC2) (vv crfM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.1, hD.2.2.2.1⟩
      ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 hL (by simp +decide [Env.get, hF]) (by simp +decide [Env.get, hP])
      (by simp +decide [Env.get, hN]) (by simp +decide [Env.get, hC2]) (by simp +decide [Env.get])
      (fun rm H2 pm2 w2 hp2 hrep2 => ?_)
    exact specR_alInsI hok h rm.1 pm2 rm.2 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
      (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep2 (h0.trans (hp1.trans hp2))

theorem specR_alArm3I {C : Ctx} (hok : CtxOK C) (hc : AlCodes C) {o : Nat} {xs : List NIdx}
    {ks : List ConLeche.Name} {n : Nat} (ih : AlRec (σ := σ) C o xs ks n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 c2 c3 : EIdx) (pm : BitVec 64)
    (memo : ALM) (K K2 : Bool × ALM → AM (Bool × ALM)) (hKf : ∀ m, K (false, m) = pure (false, m) >>= (fun y => pure (y.1, y.2.insert h y.1)))
    (hKt : ∀ m, K (true, m) = allLevelParamsDefinedGo ks m n c2 >>= K2)
    (hK2f : ∀ m, K2 (false, m) = pure (false, m) >>= (fun y => pure (y.1, y.2.insert h y.1)))
    (hK2t : ∀ m, K2 (true, m) = allLevelParamsDefinedGo ks m n c3 >>= (fun y => pure (y.1, y.2.insert h y.1)))
    (hD : crfK1 ∈ D ∧ crfK2 ∈ D ∧ crfK3 ∈ D ∧ crfR ∈ D ∧ crfM2 ∈ D ∧ crfN ∈ D ∧ crfO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : CrRep C H pm memo) (hL : LpsAt C s o xs ks)
    (hF : Γ.get crfF = some (BitVec.ofNat 64 (n + 1))) (hP : Γ.get alP = some (cellA C o))
    (hN : Γ.get alN = some (BitVec.ofNat 64 xs.length))
    (hH : Γ.get crfH = some (Enc.idxW h)) (hM : Γ.get crfM = some pm) (hC1 : Γ.get crfC1 = some (Enc.idxW c1))
    (hC2 : Γ.get crfC2 = some (Enc.idxW c2)) (hC3 : Γ.get crfC3 = some (Enc.idxW c3)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (alArm3 C) s (allLevelParamsDefinedGo ks memo n c1 >>= K)
      (PostAl (ctxH C H0) s) := by
  unfold alArm3
  refine specR_alCallI hc ih crfK1 (vv crfC1) (vv crfM) c1 pm memo ⟨hD.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hL hF hP hN (by simp +decide [hC1]) (by simp +decide [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨b1, m1⟩ := rm
  cases b1
  · simp only [hKf, pure_bind]
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_alInsI hok h false pm1 m1 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
      (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep1 (h0.trans hp1)
  · simp only [hKt]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_alCallI hc ih crfK2 (vv crfC2) (vv crfM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
      ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 hL (by simp +decide [Env.get, hF]) (by simp +decide [Env.get, hP])
      (by simp +decide [Env.get, hN]) (by simp +decide [Env.get, hC2]) (by simp +decide [Env.get])
      (fun rm H2 pm2 w2 hp2 hrep2 => ?_)
    obtain ⟨b2, m2⟩ := rm
    cases b2
    · simp only [hK2f, pure_bind]
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_alInsI hok h false pm2 m2 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
        (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep2 (h0.trans (hp1.trans hp2))
    · simp only [hK2t]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_alCallI hc ih crfK3 (vv crfC3) (vv crfM2) c3 pm2 m2 ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
        ⟨by decide, by decide⟩ ((hp.trans hp1).trans hp2) hrep2 hL (by simp +decide [Env.get, hF])
        (by simp +decide [Env.get, hP]) (by simp +decide [Env.get, hN]) (by simp +decide [Env.get, hC3])
        (by simp +decide [Env.get]) (fun rm H3 pm3 w3 hp3 hrep3 => ?_)
      exact specR_alInsI hok h rm.1 pm3 rm.2 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp +decide [Env.get, hH])
        (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep3 (h0.trans (hp1.trans (hp2.trans hp3)))


theorem view_bind2_eq {β γ : Type} (h : EIdx) (v : ENodeView) (k : ENodeView → AM β) (g : β → AM γ) (s : AState)
    (hv : s.store.view h = some v) : ((ConRon.Arena.view h >>= k) >>= g) s = (k v >>= g) s := by
  rw [bind_assoc]; exact view_bind_eq h v (fun x => k x >>= g) s hv

/-- **`allLevelParamsDefinedGo`**: the memoized walk at every fuel. -/
theorem al_spec (C : Ctx) (hok : CtxOK C) (hc : AlCodes C) (o : Nat) (xs : List NIdx) (ks : List ConLeche.Name) :
    ∀ n, n < 2 ^ 64 → AlRec (σ := σ) C o xs ks n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo H s pm hp hrep hL
    refine specR_prologue (postAl_locals _ _) (al_none _ _) ?_
    unfold alCore
    rw [allLevelParamsDefinedGo]
    exact specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
  intro hn h memo H s pm hp hrep hL
  have ih' := ih (by omega)
  obtain ⟨mxs, hm, he⟩ := id hrep
  refine specR_prologue (postAl_locals _ _) (al_none _ _) ?_
  unfold alCore
  rw [allLevelParamsDefinedGo]
  have hne := ofNat_succ_ne n (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_callPure (C := ctxH C H) crfL fMl mlParams [vv crfM, vv crfH, .const 0] mlBody
    [pm, Enc.idxW h, BitVec.ofNat 64 0] (mxs.lookup (Enc.idxW h, BitVec.ofNat 64 0)) (by decide) rfl (by decide) hc.ml
    ⟨(by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]), (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]), rfl, trivial⟩
    (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
    (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
      (ml_spec C hok hc.ml (Enc.idxW h) (BitVec.ofNat 64 0) mxs pm H s (mnodes_toH hm)))
    (fun w H' _ ⟨hw, hH'⟩ => ?_)
  subst hw; subst H'
  rw [he h]
  cases hlk : mxs.lookup (Enc.idxW h, BitVec.ofNat 64 0) with
  | some r =>
    have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_alRetI hok _ (vv crfM) r pm memo (by decide)
      (fun w => by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
      (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) hrep (List.prefix_refl _)
  | none =>
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    dsimp only
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv crfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hsh => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    rcases v with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, vl, b⟩ | l | ⟨pn, pi, sub⟩
    · -- bvar
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI crfR (.const 1) (boolW true) (by decide) rfl ?_
      refine specR_assignI crfM2 (vv crfM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) ?_
      simp only [pure_bind]
      exact specR_alInsI hok h true pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep (List.prefix_refl _)
    · -- fvar
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P _ _ []) ?_
      refine specR_alArm1I (D := ctxLocals ++ crfLocals) hok hc ih' h ty pm memo ⟨by decide, by decide, by decide, by decide, by decide⟩
        hp (List.prefix_refl _) hrep hL ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) <;> try rfl
    · -- sort
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
      refine specR_atEntry fun t ht => ?_
      have hwf := sr_lwf ht.sr
      obtain ⟨l, hl⟩ := sr_sortDen ht.sr h u hv
      have hrl : ConRon.Arena.readLevel u s = .ok (l, s) := by
        simp only [ConRon.Arena.readLevel]; simp [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hl]
      dsimp only
      refine specR_runBind hrl ?_
      simp only [pure_bind]
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) crfR fLpd ldParams [vv crfC1, vv alP, vv alN] ldBody
        [Enc.idxW u, cellA C o, BitVec.ofNat 64 xs.length] (l.allParamsDefined ks) (by decide) rfl (by decide) hc.lp.lpd
        ⟨by simp +decide [Env.get], (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]), (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]), trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu ldParams _ rfl hlk) (lpd_spec C hc.lp s hwf hL l u H hl hp))
        (fun w H1 hp1 hw => ?_)
      subst hw
      refine specR_assignI crfM2 (vv crfM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) ?_
      exact specR_alInsI hok h _ pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) (by simp +decide [Env.get]) (by simp +decide [Env.get])
        (crRep_mono hp1 hrep) hp1
    · -- const
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW cus) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW cn) (Enc.idxW cus) [] []) ?_
      refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv crfC1) (Enc.idxW cus) (by decide) (by simp +decide [Env.get]) ?_
      refine specR_lsviewPI (C := ctxH C H) cus (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
        (by decide) (fun vl Pl hvl' _ _ => ?_)
      refine specR_atEntry fun t ht => ?_
      have hwf := sr_lwf ht.sr
      obtain ⟨vs, hvs, hlv, hvd⟩ := sr_lsDen ht.sr cus vl hvl'
      have hrl : ConRon.Arena.readLevels cus s = .ok (vs, s) := by
        simp only [ConRon.Arena.readLevels]; simp [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, hvs]
      dsimp only
      refine specR_runBind hrl ?_
      simp only [pure_bind]
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) crfR fLpa laParams [vv crfC1, vv alP, vv alN, .const 0] laBody
        [Enc.idxW cus, cellA C o, BitVec.ofNat 64 xs.length, BitVec.ofNat 64 0] (vs.all (ConLeche.Level.allParamsDefined ks))
        (by decide) rfl (by decide) hc.lp.lpa
        ⟨by simp +decide [Env.get], (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]), (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]), rfl, trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu laParams _ rfl hlk)
          (lpa_spec C hc.lp s hwf hL cus vl vs hvl' hlv hvd _ 0 H hp rfl (Nat.zero_le _)))
        (fun w H1 hp1 hw => ?_)
      subst hw
      refine specR_assignI crfM2 (vv crfM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) ?_
      exact specR_alInsI hok h _ pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) (by simp +decide [Env.get]) (by simp +decide [Env.get])
        (crRep_mono hp1 hrep) hp1
    · -- app
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW f) [Enc.idxW a] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW f) (Enc.idxW a) [] []) ?_
      refine specR_alArm2I (D := ctxLocals ++ crfLocals) hok hc ih' h f a pm memo _ (fun _ => rfl) (fun _ => rfl)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep hL ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) <;> try rfl
    · -- lam
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_alArm2I (D := ctxLocals ++ crfLocals) hok hc ih' h ty b pm memo _ (fun _ => rfl) (fun _ => rfl)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep hL ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) <;> try rfl
    · -- forallE
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_alArm2I (D := ctxLocals ++ crfLocals) hok hc ih' h ty b pm memo _ (fun _ => rfl) (fun _ => rfl)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ hp (List.prefix_refl _) hrep hL ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) <;> try rfl
    · -- letE
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' crfC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp +decide) (by simp)
        (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW vl, Enc.idxW b] []) ?_
      refine specR_loadI' crfC2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW vl) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW vl) [Enc.idxW b] []) ?_
      refine specR_loadI' crfC3 _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW vl) (Enc.idxW b) [] []) ?_
      refine specR_alArm3I (D := ctxLocals ++ crfLocals) hok hc ih' h ty vl b pm memo _ _ (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
        hp (List.prefix_refl _) hrep hL ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) <;> try rfl
    · -- lit
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI crfR (.const 1) (boolW true) (by decide) rfl ?_
      refine specR_assignI crfM2 (vv crfM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) ?_
      simp only [pure_bind]
      exact specR_alInsI hok h true pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) (by simp +decide [Env.get]) (by simp +decide [Env.get]) hrep (List.prefix_refl _)
    · -- proj
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' crfC1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW pn) (Enc.idxW sub) (Enc.limbs pi) []) ?_
      refine specR_alArm1I (D := ctxLocals ++ crfLocals) hok hc ih' h sub pm memo ⟨by decide, by decide, by decide, by decide, by decide⟩
        hp (List.prefix_refl _) hrep hL ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, alParams, ctxEnv]) <;> try rfl


theorem readNames_run (s : AState) : ∀ (xs : List NIdx) (ks : List ConLeche.Name) (hl : ks.length = xs.length),
    (∀ j (hj : j < xs.length), denoteN s.store.ns xs[j] = some (ks[j]'(by rw [hl]; exact hj))) →
    ConRon.Arena.readNames xs s = .ok (ks, s)
  | [], [], _, _ => rfl
  | x :: xs, k :: ks, hl, hd => by
    have h0 : denoteN s.store.ns x = some k := hd 0 (by simp)
    have ih := readNames_run s xs ks (by simpa using hl) (fun j hj => hd (j + 1) (by simp; omega))
    have hr : ConRon.Arena.readName x s = .ok (k, s) := by
      simp only [ConRon.Arena.readName]
      simp [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, h0]
    simp only [ConRon.Arena.readNames]
    simp [bind, StateT.bind, Except.bind, hr, ih, pure, StateT.pure, Except.pure]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

def atE := ofString "at_e"
def atP := ofString "at_p"
def atN := ofString "at_n"
def atK := ofString "at_k"
def atR := ofString "at_r"
def atParams : List MlS := [atE, atP, atN]

/-- `allLevelParamsDefined`: the walk from an empty memo, its answer read off the pair block. -/
def atBody : ProgHOL 64 := prologue [atK, atR]
  (.seq (.call (some (some (.local, atK), none)) fAl
    [.const (BitVec.ofNat 64 coreWalkFuel), vv atE, .const 0, vv atP, vv atN])
  (.seq (.assign .local atR (.load .one (vv atK))) (.return (vv atR))))

theorem at_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ [atK, atR] → (ctxEnv C ++ atParams.zip vals).get x = none :=
  Knot.params_none C [atK, atR] atParams vals (by decide) (by decide)

/-- **`allLevelParamsDefined`** at the parameter block. -/
theorem at_spec (C : Ctx) (hok : CtxOK C) (hc : AlCodes C) (s : AState) (e : EIdx) {o : Nat} {xs : List NIdx}
    {ks : List ConLeche.Name} (hL : LpsAt C s o xs ks) :
    SpecR (σ := σ) (Pre C s (atParams.zip [Enc.idxW e, cellA C o, BitVec.ofNat 64 xs.length])) atBody s
      (allLevelParamsDefined xs e) (PostB C) := by
  refine specR_prologue (postB_locals C) (at_none C _) ?_
  unfold allLevelParamsDefined
  refine specR_runBind (readNames_run s xs ks hL.len hL.den) ?_
  refine specR_callNIH (C := C) atK fAl alParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv atE, .const 0, vv atP, vv atN]
    (alBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0, cellA C o, BitVec.ofNat 64 xs.length] (by decide) rfl
    (by decide) hc.self
    ⟨rfl, by simp +decide [Env.get, atParams, ctxEnv], rfl, by simp +decide [Env.get, atParams, ctxEnv],
      by simp +decide [Env.get, atParams, ctxEnv], trivial⟩ (PostAl C s)
    (fun rm w _ H' => ∃ o, w = cellA C o ∧ H'[o]? = some (boolW rm.1))
    (fun rm w s' st ⟨⟨H', o, pm, hp', hw, h0, _, _, hsr⟩, _⟩ => ⟨H', hp', ⟨o, hw, h0⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu alParams _ rfl hlk)
      (al_spec C hok hc o xs ks coreWalkFuel CV.coreWalkFuel_lt e ∅ C.H s 0 (List.prefix_refl _) (crRep_empty C C.H) hL))
    (fun rm w s1 H1 hp1 ⟨o, hw, h0⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) atR (vv atK) o (boolW rm.1) h0 (by decide) (by simp [Env.get]; rfl) ?_
  exact specR_returnI _ (boolW rm.1) (by simp +decide [Env.get])
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
