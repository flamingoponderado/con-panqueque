import ConPanqueque.Front.DeclRel
import ConPanqueque.Scan.Safe

/-! # Definition records into the registry (`processLineCoreD` at `.defn`)

The name's, type's and value's handles from the tables, the safety (`"safe"`, else rejected), the
hint's value, the level parameters as a block of name handles, then a six-cell record and a registry
entry.  When every lookup succeeds and the safety is `safe`, the twin's step is a pure push. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec DeclRec HintsRec scanNatList scanString scanHints)

variable {σ : Type}

/-- The twin's hint conversion. -/
def convHint : HintsRec → ConLeche.ReducibilityHint
  | .«abbrev» => .«abbrev»
  | .«opaque» => .«opaque»
  | .regular n => .regular n

theorem hintN_conv (x : HintsRec) : T.hintN (convHint x) = Scan.hintN x := by
  cases x <;> rfl

theorem mapM_name_ok (st : StateD) :
    ∀ (us : List Nat), (∀ j (hj : j < us.length), (st.names.get? us[j]).isSome) →
      us.mapM st.name = pure (us.map (fun x => (st.names.get? x).getD default))
  | [], _ => rfl
  | x :: xs, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hx, hhx⟩ := Option.isSome_iff_exists.mp h0
    have ih := mapM_name_ok st xs (fun j hj => by have := h (j + 1) (by simp; omega); simpa using this)
    simp [List.mapM_cons, StateD.name, hhx, ih]

/-- **The twin's step on a safe definition whose indices are all bound** is a pure push. -/
theorem processDefn_ok (st : StateD) (cv : CVRec) (vl : Nat) (hints : HintsRec) (nmh : NIdx) (tyh vlh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hvl : st.exprs.get? vl = some vlh) (hlps : ∀ j (hj : j < cv.levelParams.length),
      (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.defn cv vl hints "safe") =
      pure (.inl { st with decls := st.decls.push (.defnDecl
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩ vlh (convHint hints)) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  cases hints <;>
  simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hvl, hm, pushDecl, convHint]

/-- `x := f(a₁, a₂, a₃)` at a pure callee with a determined answer, as a step. -/
theorem step_call3I {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (x f x1 x2 x3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 v : BitVec 64)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetSpec (callEntryStateHOLFinite t callee) body v) :
    Step (σ := σ) (Inv C s Γ M D) (callTo x f [a1, a2, a3]) (Inv C s ((x, v) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  rcases call3_ret t x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 v w0 h12 h13 h23 (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) hw0 (fun callee h1 h2 h3 => hbody t callee ht h1 h2 h3) with
    hs | ⟨u, hu, m1, d1, g1, c1, b1, lx, lo⟩
  · exact Or.inl hs
  simp only [callTo]
  rw [hu]
  refine Or.inr ⟨rfl, sr_of_eq ht.sr m1 d1 g1 c1, fun y v' hy => ?_, fun a v' ha => by rw [m1, d1]; exact ht.mem a v' ha,
    fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact lx
    · rename_i e; rw [lo y e]; exact ht.env y v' hy
  · by_cases e : y = x
    · subst e; exact ⟨v, lx⟩
    · rw [lo y e]; exact ht.decl y hy

/-- `x := f(a₁, a₂, a₃)` at a pure callee specified by `RetP`, as a step keeping the callee's fact. -/
theorem step_call3P {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (x f x1 x2 x3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 : BitVec 64) (P : BitVec 64 → Prop)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetP (callEntryStateHOLFinite t callee) body P) :
    Step (σ := σ) (Inv C s Γ M D) (callTo x f [a1, a2, a3]) (fun t => ∃ w, P w ∧ Inv C s ((x, w) :: Γ) M D t) := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  rcases call3_retP t x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 w0 P h12 h13 h23 (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) hw0 (fun callee h1 h2 h3 => hbody t callee ht h1 h2 h3) with
    hs | ⟨w, u, hp, hu, m1, d1, g1, c1, b1, lx, lo⟩
  · exact Or.inl hs
  simp only [callTo]
  rw [hu]
  refine Or.inr ⟨rfl, w, hp, sr_of_eq ht.sr m1 d1 g1 c1, fun y v' hy => ?_,
    fun a v' ha => by rw [m1, d1]; exact ht.mem a v' ha, fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact lx
    · rename_i e; rw [lo y e]; exact ht.env y v' hy
  · by_cases e : y = x
    · subst e; exact ⟨w, lx⟩
    · rw [lo y e]; exact ht.decl y hy

/-- The heap image keeps every cell below the frontier other than the registry's. -/
def AgreeBelow (F rb capD : Nat) (H H' : List (BitVec 64)) : Prop :=
  ∀ c, c < F → (c < rb ∨ rb + 1 + capD ≤ c) → H'[c]? = H[c]?

theorem tblRel_agree {k : IdxKind} {F rb capD : Nat} {H H' : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (h : TblRel H j cap tbl) (ha : AgreeBelow F rb capD H H') (hjF : j + cap ≤ F)
    (hjr : j + cap ≤ rb ∨ rb + 1 + capD ≤ j) : TblRel H' j cap tbl :=
  ⟨fun i hi => by rw [ha (j + i) (by omega) (by omega)]; exact h.1 i hi, h.2⟩

theorem packed_agree {F rb capD : Nat} {H H' : List (BitVec 64)} {j0 : Nat} {bs : List UInt8} (h : Packed H j0 bs)
    (ha : AgreeBelow F rb capD H H') (hF : ∀ i, i < bs.length → j0 + i / 8 < F ∧ (j0 + i / 8 < rb ∨ rb + 1 + capD ≤ j0 + i / 8)) :
    Packed H' j0 bs := fun i hi => by
  obtain ⟨w, hw, hb⟩ := h i hi
  exact ⟨w, by rw [ha _ (hF i hi).1 (hF i hi).2]; exact hw, hb⟩

/-- Store `es` at cells `j, j+1, …` from the address in `kb`. -/
def storesP (kb : MlS) : Nat → List (ExpHOL 64) → ProgHOL 64 → ProgHOL 64
  | _, [], rest => rest
  | j, e :: es, rest => .seq (.store (.op .add [vv kb, .const (BitVec.ofNat 64 (8 * j))]) e) (storesP kb (j + 1) es rest)

theorem kcH_succ (H : List (BitVec 64)) (o : Nat) (ws : List (BitVec 64)) (n : Nat) :
    kcH H o ws (n + 1) = (kcH H o ws n).set (o + n) (ws.getD n 0) := rfl

/-- The stores, by induction: the image afterwards is `kcH` of the words from `r`. -/
theorem storesP_spec {α : Type} (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (D : List MlS) (kb : MlS)
    (r : Nat) (hkb : Γ.get kb = some (cellA C r)) (ws : List (BitVec 64)) {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64) :
    ∀ (es : List (ExpHOL 64)) (j : Nat) (H : List (BitVec 64)), j + es.length ≤ ws.length →
      r + ws.length ≤ H.length → 8 * (r + ws.length) < 2 ^ 64 →
      (∀ i (hi : i < es.length), sev Γ es[i] = some (ws.getD (j + i) 0)) →
      SpecR (Inv (ctxH C (kcH H r ws (j + es.length))) s Γ [] D) rest s m R →
      SpecR (Inv (ctxH C (kcH H r ws j)) s Γ [] D) (storesP kb j es rest) s m R
  | [], j, H, _, _, _, _, h => h
  | e :: es, j, H, hl, hH, h8, he, h => by
    simp only [List.length_cons] at hl
    have hlen : (kcH H r ws j).length = H.length := kcH_length _ _ _ _
    refine specR_heapStoreI (C := ctxH C (kcH H r ws j)) (ctxOK_H hok _) _ e (r + j) (by simp only [ctxH]; omega)
      (ws.getD j 0)
      (by simp only [sev, vv, hkb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rw [← cellA_add]; rfl)
      (by have := he 0 (by simp); simpa using this) ?_
    refine storesP_spec C hok s Γ D kb r hkb ws rest es (j + 1) H (by omega) hH h8
      (fun i hi => by have := he (i + 1) (by simp; omega); simpa [show j + (i + 1) = j + 1 + i by omega] using this)
      (by simpa [show j + 1 + es.length = j + (es.length + 1) by omega] using h)

def kRB := ofString "krb"
def kCapD := ofString "kcapd"
def kCnt := ofString "kcnt"
def kR := ofString "kr"

/-- Append the record at `kR` to the registry at `kRB`. -/
def regPushP : ProgHOL 64 :=
  .seq (.assign .local kCnt (.load .one (vv kRB)))
    (.ite (.cmp .lower (vv kCnt) (vv kCapD))
      (.seq (.store (.op .add [.op .add [vv kRB, .const 8], .shift .lsl (vv kCnt) (.const 3)]) (vv kR))
        (.seq (.store (vv kRB) (.op .add [vv kCnt, .const 1])) (.return (.const 0))))
      hang)

/-- After a declaration record: the twin pushed `d`; the image agrees with the starting one below the
frontier (registry aside) and holds the registry with `d` appended. -/
def DeclPost (C : Ctx) (F rb capD : Nat) (H0 : List (BitVec 64)) (st : StateD) (d : IDeclaration) :
    StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop :=
  fun a _ s' t' => a = .inl { st with decls := st.decls.push d } ∧ ∃ H', SR (ctxH C H') s' t' ∧
    AgreeBelow F rb capD H0 H' ∧ H0.length ≤ H'.length ∧ DeclsRel C F rb capD H' (st.decls.push d)

theorem regPush_spec (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (D : List MlS) (hD : kCnt ∈ D)
    (F rb capD : Nat) (H0 H : List (BitVec 64)) (st : StateD) (d : IDeclaration) (r : Nat)
    (hag : AgreeBelow F rb capD H0 H) (hlen : H0.length ≤ H.length)
    (hrel : DeclsRel C F rb capD H st.decls) (hrec : RecEnc C F H r d) (hcap : 8 * (rb + 1 + capD) < 2 ^ 64)
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hR : Γ.get kR = some (cellA C r)) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ [] D) regPushP s
      (pure (.inl { st with decls := st.decls.push d })) (DeclPost C F rb capD H0 st d) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrel
  have hrbl : rb < H.length := by omega
  unfold regPushP
  have hHrb : H[rb] = BitVec.ofNat 64 st.decls.size := by
    rw [List.getElem?_eq_getElem hrbl] at h1; exact Option.some.inj h1
  refine specR_heapLoadI (C := ctxH C H) kCnt (vv kRB) rb hrbl hD (by simp only [sev, vv]; exact hRB) ?_
  simp only [ctxH, hHrb]
  have g1 : ∀ y, y ≠ kCnt → Env.get ((kCnt, BitVec.ofNat 64 st.decls.size) :: Γ) y = Env.get Γ y := fun y h => by
    rw [Env.get_cons, ite_eq_right h]
  refine specR_ifI _ _ (sev_lower _ (vv kCnt) (vv kCapD) st.decls.size capD (by simp [sev, vv, Env.get_cons])
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hCD) (by omega) (by omega)) (fun hw => ?_)
    (fun _ => specR_hangI)
  have hk : st.decls.size < capD := by
    by_cases h : st.decls.size < capD
    · exact h
    · simp [bw, h] at hw
  let k := st.decls.size
  refine specR_heapStoreI (C := ctxH C H) (ctxOK_H hok _) _ (vv kR) (rb + 1 + k) (by simp only [ctxH]; omega)
    (cellA C r)
    (by simp only [sev, vv]; rw [g1 _ (by decide), hRB, Env.get_cons, ite_eq_left rfl]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
          show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, ite_true]
        rw [shl3 k (by omega), show (8 : BitVec 64) = BitVec.ofNat 64 (8 * 1) from rfl, ← cellA_add, ← cellA_add]; rfl)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hR) ?_
  let H1 := H.set (rb + 1 + k) (cellA C r)
  refine specR_heapStoreI (C := ctxH C H1) (ctxOK_H hok _) (vv kRB) _ rb (by simp only [ctxH, H1]; simp; omega)
    (BitVec.ofNat 64 (k + 1)) (by simp only [sev, vv]; rw [g1 _ (by decide), hRB]; rfl)
    (by simp only [sev, vv, Env.get_cons, ite_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr 1; apply BitVec.eq_of_toNat_eq; simp only [k, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega) ?_
  refine specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, H1.set rb (BitVec.ofNat 64 (k + 1)),
    sr_of_eq ht.sr rfl rfl rfl rfl, fun c hc hcr => ?_, by simp [H1]; omega, ?_⟩)
  · show ((H.set (rb + 1 + k) (cellA C r)).set rb (BitVec.ofNat 64 (k + 1)))[c]? = _
    rw [List.getElem?_set, ite_eq_right (by omega), List.getElem?_set, ite_eq_right (by omega)]
    exact hag c hc hcr
  · refine ⟨by simp [H1, List.getElem?_set, hrbl]; rfl, by simp; omega, h3, by simp [H1]; omega, fun k' hk' => ?_⟩
    simp only [Array.size_push] at hk'
    by_cases e : k' = k
    · subst e
      refine ⟨r, ?_, ?_⟩
      · show ((H.set (rb + 1 + k) (cellA C r)).set rb (BitVec.ofNat 64 (k + 1)))[rb + 1 + k]? = _
        rw [List.getElem?_set, ite_eq_right (by omega), List.getElem?_set, ite_eq_left rfl, ite_eq_left (by omega)]
      · simp only [k, Array.getElem_push_eq]
        exact recEnc_set (recEnc_set hrec _ (by omega) _) _ (by omega) _
    · obtain ⟨o, ho, hro⟩ := h5 k' (by omega)
      refine ⟨o, ?_, ?_⟩
      · show ((H.set (rb + 1 + k) (cellA C r)).set rb (BitVec.ofNat 64 (k + 1)))[rb + 1 + k']? = _
        rw [List.getElem?_set, ite_eq_right (by omega), List.getElem?_set, ite_eq_right (by omega)]; exact ho
      · rw [Array.getElem_push_lt (by omega)]
        exact recEnc_set (recEnc_set hro _ (by omega) _) _ (by omega) _

theorem blkAt_set_above {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (j : Nat)
    (hj : o + 1 + xs.length ≤ j) (w : BitVec 64) : BlkAt (H.set j w) o xs :=
  ⟨by rw [List.getElem?_set, ite_eq_right (by omega)]; exact h.1,
   fun i hi => by rw [List.getElem?_set, ite_eq_right (by omega)]; exact h.2 i hi⟩

theorem blkAt_kcH {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (r : Nat)
    (hr : o + 1 + xs.length ≤ r) (ws : List (BitVec 64)) : ∀ n, BlkAt (kcH H r ws n) o xs
  | 0 => h
  | n + 1 => blkAt_set_above (blkAt_kcH h r hr ws n) _ (by omega) _

theorem getElem?_set_ext {H H' : List (BitVec 64)} (hp : H <+: H') {c j : Nat} {v w : BitVec 64}
    (h : H[c]? = some v) (hj : H.length ≤ j) : (H'.set j w)[c]? = some v := by
  have hl : c < H.length := by
    by_cases hl : c < H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [List.getElem?_set, ite_eq_right (by omega)]; exact getElem?_prefix hp h

theorem blkAt_set_ext {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs)
    (j : Nat) (hj : H.length ≤ j) (w : BitVec 64) : BlkAt (H'.set j w) o xs :=
  ⟨getElem?_set_ext hp h.1 hj, fun i hi => getElem?_set_ext hp (h.2 i hi) hj⟩

theorem recEnc_set_ext {C : Ctx} {F : Nat} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {d : IDeclaration}
    (h : RecEnc C F H o d) (j : Nat) (hj : H.length ≤ j) (w : BitVec 64) : RecEnc C F (H'.set j w) o d := by
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨ho, h1, ⟨ol, hol, c1, c2, c3, c4, c5⟩, h3, h4, h5⟩ := h
    exact ⟨ho, getElem?_set_ext hp h1 hj, ⟨ol, hol, getElem?_set_ext hp c1 hj, getElem?_set_ext hp c2 hj,
      getElem?_set_ext hp c3 hj, blkAt_set_ext hp c4 j hj w, c5⟩, getElem?_set_ext hp h3 hj,
      getElem?_set_ext hp h4 hj, h5⟩
  | thmDecl cv v =>
    obtain ⟨ho, h1, ⟨ol, hol, c1, c2, c3, c4, c5⟩, h3⟩ := h
    exact ⟨ho, getElem?_set_ext hp h1 hj, ⟨ol, hol, getElem?_set_ext hp c1 hj, getElem?_set_ext hp c2 hj,
      getElem?_set_ext hp c3 hj, blkAt_set_ext hp c4 j hj w, c5⟩, getElem?_set_ext hp h3 hj⟩
  | opaqueDecl cv v =>
    obtain ⟨ho, h1, ⟨ol, hol, c1, c2, c3, c4, c5⟩, h3⟩ := h
    exact ⟨ho, getElem?_set_ext hp h1 hj, ⟨ol, hol, getElem?_set_ext hp c1 hj, getElem?_set_ext hp c2 hj,
      getElem?_set_ext hp c3 hj, blkAt_set_ext hp c4 j hj w, c5⟩, getElem?_set_ext hp h3 hj⟩
  | _ => exact h.elim

/-- Writes past an image keep its registry, on any extension. -/
theorem declsRel_kcH {C : Ctx} {F rb capD : Nat} {H H' : List (BitVec 64)} {decls : Array IDeclaration}
    (h : DeclsRel C F rb capD H decls) (hp : H <+: H') (r : Nat) (hr : H.length ≤ r) (ws : List (BitVec 64)) :
    ∀ n, DeclsRel C F rb capD (kcH H' r ws n) decls
  | 0 => declsRel_prefix h hp
  | n + 1 => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have ih := declsRel_kcH ⟨h1, h2, h3, h4, h5⟩ hp r hr ws n
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    have hpk : H <+: kcH H' r ws n := prefix_kcH hp r hr ws n
    refine ⟨getElem?_set_ext hpk h1 (by omega), h2, h3, by simp [kcH_length]; have := hp.length_le; omega,
      fun k hk => ?_⟩
    obtain ⟨o, ho, hro⟩ := h5 k hk
    exact ⟨o, getElem?_set_ext hpk ho (by omega), recEnc_set_ext hpk hro _ (by omega) _⟩

/-- A table read at a capped index succeeds only at the true index (the cap is past every table). -/
theorem get_capped {k : IdxKind} {H : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (hrel : TblRel H j cap tbl) (hcapN : cap ≤ natCap) (x : Nat) (h : Idx k)
    (hh : tbl.get? (min x natCap) = some h) : tbl.get? x = some h := by
  by_cases hl : x < natCap
  · rwa [show min x natCap = x by omega] at hh
  · rw [show min x natCap = natCap by omega, hrel.2 natCap hcapN] at hh; cases hh

def kVl := ofString "kvl"
def kVh := ofString "kvh"
def kSf := ofString "ksf"
def kHn := ofString "khn"
def kHv := ofString "khv"
def kT := ofString "kt"

/-- A `def` record: `fU` the name's index, `fV2` the level-parameter slot, `fW3` the type's index,
`kVl` the value's index, `kHn` the hints slot, `kSf` the safety slot. -/
def dfP (C : Ctx) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblGetP fz (vv fTE) (vv fCap) (vv fW3)
      (tblGetP kVh (vv fTE) (vv fCap) (vv kVl)
        (.ite (.cmp .equal (vv kSf) (.const (BitVec.ofNat 64 listSentinel))) hang
          (.seq (callTo kT fSafe [vv kBA, vv kBN, vv kSf])
            (.seq (.ite (.cmp .equal (vv kHn) (.const (BitVec.ofNat 64 listSentinel)))
                (.assign .local kHv (.const 2)) (callTo kHv fHintV [vv kBA, vv kBN, vv kHn]))
              (lstBlkP C fTN
                (allocP C kR (.const (BitVec.ofNat 64 48))
                  (storesP kR 0 [.const 1, vv fy, vv kKA0, vv fz, vv kVh, vv kHv] regPushP))))))))

theorem scanString_lt {b : ByteArray} (hp : Plat b) {p e : USize} {x : String}
    (h : scanString b p = .ok x e) : p.toNat < b.size := by
  rw [scanString] at h
  split at h
  · simp at h
  · rename_i hb
    by_cases hl : p.toNat < b.size
    · exact hl
    · have : ConLeche.Frontend.byteAt b p = 0 := by
        rw [byteAt_eq hp p]; simp [List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ p.toNat)]
      rw [this] at hb; simp at hb

theorem scanHints_det {b : ByteArray} {p e e' : USize} {x x' : HintsRec}
    (h : scanHints b p = .ok x e) (h' : scanHints b p = .ok x' e') : x = x' := by
  rw [h] at h'; simp only [ConLeche.Frontend.ScanRes.ok.injEq] at h'; exact h'.1

theorem scanHints_lt {b : ByteArray} (hp : Plat b) {p e : USize} {x : HintsRec}
    (h : scanHints b p = .ok x e) : p.toNat < b.size := by
  by_cases hl : p.toNat < b.size
  · exact hl
  · have : ConLeche.Frontend.byteAt b p = 0 := by
      rw [byteAt_eq hp p]; simp [List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ p.toNat)]
    rw [scanHints, this] at h; simp at h

/-- The frontend's layout below the frontier: the tables, the buffer and the registry. -/
structure FrontLay (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) : Prop where
  tN : jN + cap ≤ rb
  tL : jL + cap ≤ rb
  tE : jE + cap ≤ rb
  buf : rb + 1 + capD ≤ bufJ
  bufF : bufJ + b.size / 8 + 1 ≤ F

theorem dfP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcS : C.code.lookup fSafe = some ([(sB, .one), (sN, .one), (sI, .one)], sfFun, .one))
    (hcH : C.code.lookup fHintV = some ([(sB, .one), (sN, .one), (sI, .one)], hvFun, .one))
    (hhc : ∀ t : PState σ, t.code = C.code → HvCodes t)
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fy, fz, kVh, kT, kHv, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (cv : CVRec) (vl : Nat) (hints : HintsRec) (safety : String) (hus : cv.levelParams.length < 2 ^ 59)
    (wpos wh wsf : BitVec 64)
    (hslot : (∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ scanNatList b pos = .ok cv.levelParams e0) ∨
      (cv.levelParams = [] ∧ wpos = BitVec.ofNat 64 listSentinel))
    (hhs : (∃ (p e : USize), wh = BitVec.ofNat 64 p.toNat ∧ scanHints b p = .ok hints e) ∨
      (hints = .regular 0 ∧ wh = BitVec.ofNat 64 listSentinel))
    (hss : (∃ (p e : USize), wsf = BitVec.ofNat 64 p.toNat ∧ scanString b p = .ok safety e) ∨
      (safety = "" ∧ wsf = BitVec.ofNat 64 listSentinel))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hU : Γ.get fU = some (BitVec.ofNat 64 (min cv.name natCap)))
    (hW : Γ.get fW3 = some (BitVec.ofNat 64 (min cv.type natCap)))
    (hVl : Γ.get kVl = some (BitVec.ofNat 64 (min vl natCap)))
    (hV : Γ.get fV2 = some wpos) (hHn : Γ.get kHn = some wh) (hSf : Γ.get kSf = some wsf)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (dfP C) s (processLineCoreD st (.defn cv vl hints safety))
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hplat := hbuf.plat
  have hsmall := hbuf.small
  have hNC : min cv.name natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hTC : min cv.type natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hVC : min vl natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  unfold dfP
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) _ hNC (by simpa [sev, vv] using hU)
    (fun nmh hnm => ?_)
  have hnm' := get_capped hreln hcapN _ nmh hnm
  have g1 : ∀ y, y ≠ fy → Env.get ((fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ) y = Env.get Γ y :=
    fun y h => by simp only [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv fW3)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    _ hTC (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hW) (fun tyh hty => ?_)
  have hty' := get_capped hrele hcapN _ tyh hty
  let Γ2 : Env := (fz, Enc.idxW tyh) :: (fz, Enc.idxW tyh + 1) :: (fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ
  have g2 : ∀ y, y ≠ fz → y ≠ fy → Env.get Γ2 y = Env.get Γ y := fun y h1 h2 => by
    simp only [Γ2, Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  refine specR_tblGetI kVh (hD kVh (by simp)) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv kVl)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hC) _ hVC
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hVl) (fun vlh hvh => ?_)
  have hvl' := get_capped hrele hcapN _ vlh hvh
  let Γ3 : Env := (kVh, Enc.idxW vlh) :: (kVh, Enc.idxW vlh + 1) :: Γ2
  have g3 : ∀ y, y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ3 y = Env.get Γ y := fun y h0 h1 h2 => by
    simp only [Γ3, Env.get_cons, ite_eq_right h0]; exact g2 y h1 h2
  have hsent : ∀ (p : USize), p.toNat ≤ b.size → BitVec.ofNat 64 p.toNat ≠ BitVec.ofNat 64 listSentinel := by
    intro p hp e
    have := congrArg BitVec.toNat e
    simp [listSentinel] at this; omega
  refine specR_ifI _ _ (sev_eq_c' Γ3 kSf wsf (BitVec.ofNat 64 listSentinel)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hSf)) (fun _ => specR_hangI) (fun hw => ?_)
  have hw' : wsf ≠ BitVec.ofNat 64 listSentinel := by intro h; simp [bw, h] at hw
  obtain ⟨psf, esf, hwsf, hsf⟩ := hss.resolve_right (fun ⟨_, h⟩ => hw' h)
  have hpsf : psf.toNat ≤ b.size := Nat.le_of_lt (scanString_lt hplat hsf)
  have hbt : ∀ (t : PState σ) (Δ : Env) (M' : Mem), Inv C s Δ M' D t → BytesAt t (cellA C bufJ) b.data.toList :=
    fun t Δ M' ht => bufOK_bytes (H := C.H) hok hbuf (by rw [ctxH_self]; exact ht) hbuf.pk (Nat.le_refl _)
  refine specR_retP3 kT fSafe sB sN sI sfFun (vv kBA) (vv kBN) (vv kSf) (cellA C bufJ) (BitVec.ofNat 64 b.size)
    (BitVec.ofNat 64 psf.toNat) (fun _ => safety = "safe") (by decide) (by decide) (by decide) (hD kT (by simp)) hcS
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by simp only [sev, vv]; rw [g3 _ (by decide) (by decide) (by decide), hSf, hwsf])
    (fun t callee ht h1 h2 h3 => sfFun_sound (callEntryStateHOLFinite t callee) (cellA C bufJ) b hplat
      (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl) psf hpsf safety esf hsf h1 h2 h3) (fun wt hsafe => ?_)
  subst hsafe
  let Γ4 : Env := (kT, wt) :: Γ3
  have g4 : ∀ y, y ≠ kT → y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ4 y = Env.get Γ y := fun y h h0 h1 h2 => by
    simp only [Γ4, Env.get_cons, ite_eq_right h]; exact g3 y h0 h1 h2
  -- the hint's value
  refine specR_step (Q := fun t => Inv C s ((kHv, BitVec.ofNat 64 (Scan.hintN hints)) :: Γ4) M D t ∧
    Scan.hintN hints < 2 ^ 63) ?_ ?_
  · refine step_ifI _ _ (sev_eq_c' Γ4 kHn wh (BitVec.ofNat 64 listSentinel)
      (by rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hHn)) (fun hw2 => ?_) (fun hw2 => ?_)
    · have hw2' : wh = BitVec.ofNat 64 listSentinel := by
        by_cases h : wh = BitVec.ofNat 64 listSentinel
        · exact h
        · simp [bw, h] at hw2
      have hreg : hints = .regular 0 := by
        rcases hhs with ⟨p, e, hwp, hsc⟩ | ⟨h0, _⟩
        · exact absurd (hwp.symm.trans hw2') (hsent p (Nat.le_of_lt (scanHints_lt hplat hsc)))
        · exact h0
      subst hreg
      exact step_mono (step_assignI kHv (.const 2) _ (hD kHv (by simp)) rfl) (fun t ht => ht)
        (fun t ht => ⟨ht, by simp [Scan.hintN]⟩)
    · have hw2' : wh ≠ BitVec.ofNat 64 listSentinel := by intro h; simp [bw, h] at hw2
      obtain ⟨ph, eh, hwh, hsc⟩ := hhs.resolve_right (fun ⟨_, h⟩ => hw2' h)
      have hph : ph.toNat ≤ b.size := Nat.le_of_lt (scanHints_lt hplat hsc)
      refine step_mono (step_call3P kHv fHintV sB sN sI hvFun (vv kBA) (vv kBN) (vv kHn) (cellA C bufJ)
        (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 ph.toNat) (HvQ b ph) (by decide) (by decide) (by decide)
        (hD kHv (by simp)) hcH
        (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBA)
        (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide)]; exact hBN)
        (by simp only [sev, vv]; rw [g4 _ (by decide) (by decide) (by decide) (by decide), hHn, hwh])
        (fun t callee ht h1 h2 h3 => hvFun_sound (callEntryStateHOLFinite t callee)
          (cellA C bufJ) b hplat (bytesAt_congr (t := t) (hbt t _ _ ht) rfl rfl rfl)
          (hhc _ (by show t.code = C.code; exact ht.sr.code)) ph hph h1 h2 h3)) (fun t ht => ht) ?_
      intro t ⟨w, ⟨x, e', hx, hw, hb⟩, ht⟩
      rw [scanHints_det hx hsc] at hw hb
      subst hw
      exact ⟨ht, hb⟩
  by_cases hbound : Scan.hintN hints < 2 ^ 63
  swap
  · intro t ⟨_, hb⟩; exact absurd hb hbound
  refine specR_mono (P := Inv C s ((kHv, BitVec.ofNat 64 (Scan.hintN hints)) :: Γ4) M D) ?_ (fun t ht => ht.1)
    (fun _ _ _ _ h => h)
  let Γ5 : Env := (kHv, BitVec.ofNat 64 (Scan.hintN hints)) :: Γ4
  have g5 : ∀ y, y ≠ kHv → y ≠ kT → y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ5 y = Env.get Γ y :=
    fun y h h' h0 h1 h2 => by simp only [Γ5, Env.get_cons, ite_eq_right h]; exact g4 y h' h0 h1 h2
  have hFH : F ≤ C.H.length := hdr.2.2.2.1
  refine lstBlk_spec C hok hnc hcN s Γ5 M D (fun x hx => hD x (by simp [hx])) fTN (by decide) st.names jN cap hreln hcap
    hcapN bufJ b hbuf cv.levelParams (by omega) wpos hslot
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g5 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hV) _
    (fun H' o Γ' hp' ho hblk hall hka0 hkeep => ?_)
  -- the twin: a pure push
  rw [processDefn_ok st cv vl hints nmh tyh vlh hnm' hty' hvl' hall]
  let lpsH := cv.levelParams.map (fun x => (st.names.get? x).getD default)
  let d : IDeclaration := .defnDecl ⟨nmh, lpsH, tyh⟩ vlh (convHint hints)
  have look : ∀ y, y ∉ lbMods → y ≠ kHv → y ≠ kT → y ≠ kVh → y ≠ fz → y ≠ fy → Γ'.get y = Γ.get y :=
    fun y hm h h' h0 h1 h2 => by rw [hkeep y hm]; exact g5 y h h' h0 h1 h2
  have hblkH := hblk
  have hbl1 : o + 1 + cv.levelParams.length ≤ H'.length := by
    have := hblk.2 (cv.levelParams.length - 1)
    by_cases h0 : cv.levelParams.length = 0
    · have := hblk.1
      have hl : o < H'.length := by
        by_cases hl : o < H'.length
        · exact hl
        · rw [List.getElem?_eq_none (by omega)] at this; cases this
      omega
    · have h1 := hblk.2 (cv.levelParams.length - 1) (by simp [tWords]; omega)
      by_cases hl : o + 1 + (cv.levelParams.length - 1) < H'.length
      · omega
      · rw [List.getElem?_eq_none (by omega)] at h1; cases h1
  change SpecR _ (allocP (ctxH C H') kR _ _) _ _ _
  refine specR_allocI (C := ctxH C H') kR (.const (BitVec.ofNat 64 48)) 6 (by decide) (hD kR (by simp))
    (fun v => rfl) (fun H2 wsR hp2 hwl2 hcap2 => ?_)
  have hH'2 : H'.length ≤ H2.length := hp2.length_le
  let r := H2.length
  let ws : List (BitVec 64) := [1, Enc.idxW nmh, cellA C o, Enc.idxW tyh, Enc.idxW vlh,
    BitVec.ofNat 64 (Scan.hintN hints)]
  have hlR : (H2 ++ wsR).length = H2.length + 6 := by simp [hwl2]
  have hkR : Env.get ((kR, cellA (ctxH C H') r) :: Γ') kR = some (cellA C r) := by simp [Env.get_cons]; rfl
  have gR : ∀ y, y ≠ kR → Env.get ((kR, cellA (ctxH C H') r) :: Γ') y = Γ'.get y := fun y h => by
    rw [Env.get_cons, ite_eq_right h]
  have hlay2 := hok.heapLay
  have hcap2' : H2.length + 6 ≤ C.HN := hcap2
  have lfy : Γ'.get fy = some (Enc.idxW nmh) := by
    rw [hkeep fy (by decide)]
    simp [Γ5, Γ4, Γ3, Γ2, Env.get_cons, show fy ≠ kHv from by decide, show fy ≠ kT from by decide,
      show fy ≠ kVh from by decide, show fy ≠ fz from by decide]
  have lfz : Γ'.get fz = some (Enc.idxW tyh) := by
    rw [hkeep fz (by decide)]
    simp [Γ5, Γ4, Γ3, Γ2, Env.get_cons, show fz ≠ kHv from by decide, show fz ≠ kT from by decide,
      show fz ≠ kVh from by decide]
  have lvh : Γ'.get kVh = some (Enc.idxW vlh) := by
    rw [hkeep kVh (by decide)]
    simp [Γ5, Γ4, Γ3, Env.get_cons, show kVh ≠ kHv from by decide, show kVh ≠ kT from by decide]
  have lhv : Γ'.get kHv = some (BitVec.ofNat 64 (Scan.hintN hints)) := by
    rw [hkeep kHv (by decide)]; simp [Γ5, Env.get_cons]
  refine storesP_spec C hok s _ D kR r hkR ws regPushP [.const 1, vv fy, vv kKA0, vv fz, vv kVh, vv kHv] 0
    (H2 ++ wsR) (by simp [ws]) (by simp [ws]; omega) (by simp [ws]; omega) (fun i hi => ?_) ?_
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lfy]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), hka0]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lfz]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lvh]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lhv]; rfl
  · -- the record is written: the registry entry
    let HK := kcH (H2 ++ wsR) r ws 6
    have hp0 : C.H <+: H2 ++ wsR := hp'.trans (hp2.trans (List.prefix_append _ _))
    have hgK : ∀ c, c < r → HK[c]? = (H2 ++ wsR)[c]? := fun c hc => by
      simp only [HK]; rw [kcH_get, ite_eq_right (by omega)]
    have hKr : ∀ i, i < 6 → HK[r + i]? = some (ws.getD i 0) := fun i hi => by
      simp only [HK]; rw [kcH_get, ite_eq_left ⟨by omega, by omega, by omega⟩, show r + i - r = i by omega]
    have hRB' : Env.get ((kR, cellA (ctxH C H') r) :: Γ') kRB = some (cellA C rb) := by
      rw [gR _ (by decide), look kRB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRB
    have hCD' : Env.get ((kR, cellA (ctxH C H') r) :: Γ') kCapD = some (BitVec.ofNat 64 capD) := by
      rw [gR _ (by decide), look kCapD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hCD
    have hrec : RecEnc C F HK r d := by
      refine ⟨by omega, by simpa [ws] using hKr 0 (by decide), ⟨o, by omega, by simpa [ws] using hKr 1 (by decide),
        by simpa [ws] using hKr 2 (by decide), by simpa [ws] using hKr 3 (by decide), ?_, by simpa [lpsH] using hus⟩,
        by simpa [ws] using hKr 4 (by decide), ?_, by rw [hintN_conv]; exact hbound⟩
      · have hb2 : BlkAt (H2 ++ wsR) o (tWords st.names cv.levelParams) := blkAt_mono hblk (hp2.trans (List.prefix_append _ _))
        have := blkAt_kcH hb2 r (by simp [tWords]; omega) ws 6
        have e : lpsH.map Enc.idxW = cv.levelParams.map (fun x => Enc.idxW ((st.names.get? x).getD default)) := by
          simp [lpsH]
        rw [e]; exact this
      · rw [hintN_conv]; simpa [ws] using hKr 5 (by decide)
    refine specR_mono (regPush_spec C hok s _ D (hD kCnt (by simp)) F rb capD C.H HK st d r
      (fun c hc hcr => by
        rw [hgK c (by show c < H2.length; omega)]
        obtain ⟨rr, hrr⟩ := hp0; rw [← hrr, List.getElem?_append_left (by omega)])
      (by simp [HK, kcH_length]; omega) (declsRel_kcH hdr hp0 r (by omega) ws 6) hrec hcapD hRB' hCD' hkR)
      (fun t ht => ht) (fun a w s' t' h => ⟨d, h⟩)

theorem processThm_ok (st : StateD) (cv : CVRec) (vl : Nat) (nmh : NIdx) (tyh vlh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hvl : st.exprs.get? vl = some vlh) (hlps : ∀ j (hj : j < cv.levelParams.length),
      (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.thm cv vl) =
      pure (.inl { st with decls := st.decls.push (.thmDecl
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩ vlh) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hvl, hm, pushDecl]

theorem processOpaque_ok (st : StateD) (cv : CVRec) (vl : Nat) (nmh : NIdx) (tyh vlh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hvl : st.exprs.get? vl = some vlh) (hlps : ∀ j (hj : j < cv.levelParams.length),
      (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.opaq cv vl false) =
      pure (.inl { st with decls := st.decls.push (.opaqueDecl
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩ vlh) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hvl, hm, pushDecl]

/-- The value declarations' tail: the level-parameter block, a five-cell record of kind `kd`, the
registry entry. -/
def vdTail (C : Ctx) (kd : Nat) : ProgHOL 64 :=
  lstBlkP C fTN (allocP C kR (.const (BitVec.ofNat 64 40))
    (storesP kR 0 [.const (BitVec.ofNat 64 kd), vv fy, vv kKA0, vv fz, vv kVh] regPushP))

theorem vdTail_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (lps : List Nat) (hus : lps.length < 2 ^ 59) (wpos : BitVec 64)
    (hslot : (∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ scanNatList b pos = .ok lps e0) ∨
      (lps = [] ∧ wpos = BitVec.ofNat 64 listSentinel))
    (kd : Nat) (wy wz wv : BitVec 64) (dOf : List NIdx → IDeclaration)
    (hrec : ∀ (H : List (BitVec 64)) (r o : Nat), F ≤ r → F ≤ o →
      H[r]? = some (BitVec.ofNat 64 kd) → H[r + 1]? = some wy → H[r + 2]? = some (cellA C o) →
      H[r + 3]? = some wz → H[r + 4]? = some wv →
      BlkAt H o ((lps.map (fun x => (st.names.get? x).getD default)).map Enc.idxW) →
      RecEnc C F H r (dOf (lps.map (fun x => (st.names.get? x).getD default))))
    {m : AM (StateD ⊕ RecordVerdict)}
    (hm : (∀ j (hj : j < lps.length), (st.names.get? lps[j]).isSome) →
      m = pure (.inl { st with decls := st.decls.push (dOf (lps.map (fun x => (st.names.get? x).getD default))) }))
    (hTN : Γ.get fTN = some (cellA C jN)) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hy : Γ.get fy = some wy) (hz : Γ.get fz = some wz) (hv : Γ.get kVh = some wv)
    (hV : Γ.get fV2 = some wpos)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (vdTail C kd) s m
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hFH : F ≤ C.H.length := hdr.2.2.2.1
  unfold vdTail
  refine lstBlk_spec C hok hnc hcN s Γ M D (fun x hx => hD x (by simp [hx])) fTN (by decide) st.names jN cap hreln hcap
    hcapN bufJ b hbuf lps (by omega) wpos hslot hTN hC hBA hBN hV _
    (fun H' o Γ' hp' ho hblk hall hka0 hkeep => ?_)
  rw [hm hall]
  let lpsH := lps.map (fun x => (st.names.get? x).getD default)
  let d := dOf lpsH
  have hbl1 : o + 1 + lps.length ≤ H'.length := by
    by_cases h0 : lps.length = 0
    · have := hblk.1
      have hl : o < H'.length := by
        by_cases hl : o < H'.length
        · exact hl
        · rw [List.getElem?_eq_none (by omega)] at this; cases this
      omega
    · have h1 := hblk.2 (lps.length - 1) (by simp [tWords]; omega)
      by_cases hl : o + 1 + (lps.length - 1) < H'.length
      · omega
      · rw [List.getElem?_eq_none (by omega)] at h1; cases h1
  change SpecR _ (allocP (ctxH C H') kR _ _) _ _ _
  refine specR_allocI (C := ctxH C H') kR (.const (BitVec.ofNat 64 40)) 5 (by decide) (hD kR (by simp))
    (fun v => rfl) (fun H2 wsR hp2 hwl2 hcap2 => ?_)
  have hH'2 : H'.length ≤ H2.length := hp2.length_le
  let r := H2.length
  let ws : List (BitVec 64) := [BitVec.ofNat 64 kd, wy, cellA C o, wz, wv]
  have hkR : Env.get ((kR, cellA (ctxH C H') r) :: Γ') kR = some (cellA C r) := by simp [Env.get_cons]; rfl
  have gR : ∀ y, y ≠ kR → Env.get ((kR, cellA (ctxH C H') r) :: Γ') y = Γ'.get y := fun y h => by
    rw [Env.get_cons, ite_eq_right h]
  have hlay2 := hok.heapLay
  have hcap2' : H2.length + 5 ≤ C.HN := hcap2
  have lfy : Γ'.get fy = some wy := by rw [hkeep fy (by decide)]; exact hy
  have lfz : Γ'.get fz = some wz := by rw [hkeep fz (by decide)]; exact hz
  have lvh : Γ'.get kVh = some wv := by rw [hkeep kVh (by decide)]; exact hv
  refine storesP_spec C hok s _ D kR r hkR ws regPushP [.const (BitVec.ofNat 64 kd), vv fy, vv kKA0, vv fz, vv kVh] 0
    (H2 ++ wsR) (by simp [ws]) (by simp [ws]; omega) (by simp [ws]; omega) (fun i hi => ?_) ?_
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lfy]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), hka0]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lfz]; rfl
    · simp only [sev, vv, List.getElem_cons_succ, List.getElem_cons_zero]; rw [gR _ (by decide), lvh]; rfl
  · let HK := kcH (H2 ++ wsR) r ws 5
    have hp0 : C.H <+: H2 ++ wsR := hp'.trans (hp2.trans (List.prefix_append _ _))
    have hgK : ∀ c, c < r → HK[c]? = (H2 ++ wsR)[c]? := fun c hc => by
      simp only [HK]; rw [kcH_get, ite_eq_right (by omega)]
    have hlR : (H2 ++ wsR).length = H2.length + 5 := by simp [hwl2]
    have hKr : ∀ i, i < 5 → HK[r + i]? = some (ws.getD i 0) := fun i hi => by
      simp only [HK]; rw [kcH_get, ite_eq_left ⟨by omega, by omega, by omega⟩, show r + i - r = i by omega]
    have hRB' : Env.get ((kR, cellA (ctxH C H') r) :: Γ') kRB = some (cellA C rb) := by
      rw [gR _ (by decide), hkeep kRB (by decide)]; exact hRB
    have hCD' : Env.get ((kR, cellA (ctxH C H') r) :: Γ') kCapD = some (BitVec.ofNat 64 capD) := by
      rw [gR _ (by decide), hkeep kCapD (by decide)]; exact hCD
    have hrecK : RecEnc C F HK r d := by
      refine hrec HK r o (by show F ≤ H2.length; omega) (by omega) (by simpa [ws] using hKr 0 (by decide))
        (by simpa [ws] using hKr 1 (by decide)) (by simpa [ws] using hKr 2 (by decide))
        (by simpa [ws] using hKr 3 (by decide)) (by simpa [ws] using hKr 4 (by decide)) ?_
      have hb2 : BlkAt (H2 ++ wsR) o (tWords st.names lps) := blkAt_mono hblk (hp2.trans (List.prefix_append _ _))
      have := blkAt_kcH hb2 r (by simp [tWords]; omega) ws 5
      have e : lpsH.map Enc.idxW = lps.map (fun x => Enc.idxW ((st.names.get? x).getD default)) := by simp [lpsH]
      rw [e]; exact this
    refine specR_mono (regPush_spec C hok s _ D (hD kCnt (by simp)) F rb capD C.H HK st d r
      (fun c hc hcr => by
        rw [hgK c (by show c < H2.length; omega)]
        obtain ⟨rr, hrr⟩ := hp0; rw [← hrr, List.getElem?_append_left (by omega)])
      (by simp [HK, kcH_length]; omega) (declsRel_kcH hdr hp0 r (by omega) ws 5) hrecK hcapD hRB' hCD' hkR)
      (fun t ht => ht) (fun a w s' t' h => ⟨d, h⟩)

/-- A value declaration without safety or hints: name, type and value through the tables, then the
tail with record kind `kd`. -/
def vdP (C : Ctx) (kd : Nat) : ProgHOL 64 :=
  tblGetP fy (vv fTN) (vv fCap) (vv fU)
    (tblGetP fz (vv fTE) (vv fCap) (vv fW3)
      (tblGetP kVh (vv fTE) (vv fCap) (vv kVl) (vdTail C kd)))

theorem vdP_spec (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [fy, fz, kVh, kR, kCnt] ++ lbMods, x ∈ D)
    (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (hlay : FrontLay F rb capD jN jL jE cap bufJ b)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (cv : CVRec) (vl : Nat) (hus : cv.levelParams.length < 2 ^ 59) (wpos : BitVec 64)
    (hslot : (∃ (pos e0 : USize), wpos = BitVec.ofNat 64 pos.toNat ∧ scanNatList b pos = .ok cv.levelParams e0) ∨
      (cv.levelParams = [] ∧ wpos = BitVec.ofNat 64 listSentinel))
    (kd : Nat) (mk : IConstantVal → EIdx → IDeclaration)
    (hrec : ∀ (cvh : IConstantVal) (vlh : EIdx) (H : List (BitVec 64)) (r : Nat), F ≤ r →
      H[r]? = some (BitVec.ofNat 64 kd) → CVEnc C F H (r + 1) cvh → H[r + 4]? = some (Enc.idxW vlh) →
      RecEnc C F H r (mk cvh vlh))
    {m : AM (StateD ⊕ RecordVerdict)}
    (hm : ∀ nmh tyh vlh, st.names.get? cv.name = some nmh → st.exprs.get? cv.type = some tyh →
      st.exprs.get? vl = some vlh → (∀ j (hj : j < cv.levelParams.length), (st.names.get? cv.levelParams[j]).isSome) →
      m = pure (.inl { st with decls := st.decls.push (mk ⟨nmh, cv.levelParams.map
        (fun x => (st.names.get? x).getD default), tyh⟩ vlh) }))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hU : Γ.get fU = some (BitVec.ofNat 64 (min cv.name natCap)))
    (hW : Γ.get fW3 = some (BitVec.ofNat 64 (min cv.type natCap)))
    (hVl : Γ.get kVl = some (BitVec.ofNat 64 (min vl natCap)))
    (hV : Γ.get fV2 = some wpos)
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (vdP C kd) s m
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  have hNC : min cv.name natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hTC : min cv.type natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  have hVC : min vl natCap < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold natCap; decide)
  unfold vdP
  refine specR_tblGetI fy (hD fy (by simp)) jN cap st.names hreln hcap (vv fTN) (vv fCap) (vv fU)
    (by simpa [sev, vv] using hTN) (by simpa [sev, vv] using hC) _ hNC (by simpa [sev, vv] using hU)
    (fun nmh hnm => ?_)
  have hnm' := get_capped hreln hcapN _ nmh hnm
  have g1 : ∀ y, y ≠ fy → Env.get ((fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ) y = Env.get Γ y :=
    fun y h => by simp only [Env.get_cons, ite_eq_right h]
  refine specR_tblGetI fz (hD fz (by simp)) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv fW3)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hTE) (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hC)
    _ hTC (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hW) (fun tyh hty => ?_)
  have hty' := get_capped hrele hcapN _ tyh hty
  let Γ2 : Env := (fz, Enc.idxW tyh) :: (fz, Enc.idxW tyh + 1) :: (fy, Enc.idxW nmh) :: (fy, Enc.idxW nmh + 1) :: Γ
  have g2 : ∀ y, y ≠ fz → y ≠ fy → Env.get Γ2 y = Env.get Γ y := fun y h1 h2 => by
    simp only [Γ2, Env.get_cons, ite_eq_right h1, ite_eq_right h2]
  refine specR_tblGetI kVh (hD kVh (by simp)) jE cap st.exprs hrele hcap (vv fTE) (vv fCap) (vv kVl)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hTE)
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hC) _ hVC
    (by simp only [sev, vv]; rw [g2 _ (by decide) (by decide)]; exact hVl) (fun vlh hvh => ?_)
  have hvl' := get_capped hrele hcapN _ vlh hvh
  let Γ3 : Env := (kVh, Enc.idxW vlh) :: (kVh, Enc.idxW vlh + 1) :: Γ2
  have g3 : ∀ y, y ≠ kVh → y ≠ fz → y ≠ fy → Env.get Γ3 y = Env.get Γ y := fun y h0 h1 h2 => by
    simp only [Γ3, Env.get_cons, ite_eq_right h0]; exact g2 y h1 h2
  refine vdTail_spec C hok hnc hcN s Γ3 M D (fun x hx => hD x (by simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)) st F rb capD jN jL jE cap bufJ b
    hlay hreln hcap hcapN hbuf hdr hcapD cv.levelParams hus wpos hslot kd (Enc.idxW nmh) (Enc.idxW tyh) (Enc.idxW vlh)
    (fun lpsH => mk ⟨nmh, lpsH, tyh⟩ vlh)
    (fun H r o hr ho h0 h1 h2 h3 h4 hb => hrec _ vlh H r hr h0
      ⟨o, ho, by simpa using h1, by simpa using h2, by simpa using h3, hb, by simpa using hus⟩ h4)
    (fun hall => hm nmh tyh vlh hnm' hty' hvl' hall)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hTN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hC)
    (by simp only [Γ3, Γ2, Env.get_cons, ite_eq_right (show fy ≠ kVh by decide), ite_eq_right (show fy ≠ fz by decide), ite_eq_left])
    (by simp only [Γ3, Γ2, Env.get_cons, ite_eq_right (show fz ≠ kVh by decide), ite_eq_left]) (by simp [Γ3])
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hV)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBA)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hBN)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hRB)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hCD)

theorem thmEnc (C : Ctx) (F : Nat) (cvh : IConstantVal) (vlh : EIdx) (H : List (BitVec 64)) (r : Nat) (hr : F ≤ r)
    (h0 : H[r]? = some (BitVec.ofNat 64 2)) (h1 : CVEnc C F H (r + 1) cvh) (h4 : H[r + 4]? = some (Enc.idxW vlh)) :
    RecEnc C F H r (.thmDecl cvh vlh) := ⟨hr, h0, h1, h4⟩

theorem opaqEnc (C : Ctx) (F : Nat) (cvh : IConstantVal) (vlh : EIdx) (H : List (BitVec 64)) (r : Nat) (hr : F ≤ r)
    (h0 : H[r]? = some (BitVec.ofNat 64 3)) (h1 : CVEnc C F H (r + 1) cvh) (h4 : H[r + 4]? = some (Enc.idxW vlh)) :
    RecEnc C F H r (.opaqueDecl cvh vlh) := ⟨hr, h0, h1, h4⟩

/-- The `isUnsafe` slot of an opaque record. -/
def kUs := ofString "kus"

/-- An opaque record: unsafe ones are rejected (the twin only handles safe opaques here). -/
def opP (C : Ctx) : ProgHOL 64 := .ite (vv kUs) hang (vdP C 3)

theorem opP_ifun (C : Ctx) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) {m : AM (StateD ⊕ RecordVerdict)}
    {R : StateD ⊕ RecordVerdict → BitVec 64 → AState → PState σ → Prop} (wu : BitVec 64)
    (hu : Γ.get kUs = some wu) (h : wu = 0 → SpecR (Inv (σ := σ) C s Γ M D) (vdP C 3) s m R) :
    SpecR (Inv (σ := σ) C s Γ M D) (opP C) s m R := by
  unfold opP
  refine specR_ifI _ wu (by simpa [sev, vv] using hu) (fun _ => specR_hangI) h

end ConPanqueque.Front
