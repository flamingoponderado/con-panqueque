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
    rw [Env.get_cons, if_neg h]
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
    (by simp only [sev, vv]; rw [g1 _ (by decide), hRB, Env.get_cons, if_pos rfl]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
          show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
        rw [shl3 k (by omega), show (8 : BitVec 64) = BitVec.ofNat 64 (8 * 1) from rfl, ← cellA_add, ← cellA_add]; rfl)
    (by simp only [sev, vv]; rw [g1 _ (by decide)]; exact hR) ?_
  let H1 := H.set (rb + 1 + k) (cellA C r)
  refine specR_heapStoreI (C := ctxH C H1) (ctxOK_H hok _) (vv kRB) _ rb (by simp only [ctxH, H1]; simp; omega)
    (BitVec.ofNat 64 (k + 1)) (by simp only [sev, vv]; rw [g1 _ (by decide), hRB]; rfl)
    (by simp only [sev, vv, Env.get_cons, if_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr 1; apply BitVec.eq_of_toNat_eq; simp only [k, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [show (1 : BitVec 64).toNat = 1 from rfl]; omega) ?_
  refine specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, H1.set rb (BitVec.ofNat 64 (k + 1)),
    sr_of_eq ht.sr rfl rfl rfl rfl, fun c hc hcr => ?_, by simp [H1]; omega, ?_⟩)
  · show ((H.set (rb + 1 + k) (cellA C r)).set rb (BitVec.ofNat 64 (k + 1)))[c]? = _
    rw [List.getElem?_set, if_neg (by omega), List.getElem?_set, if_neg (by omega)]
    exact hag c hc hcr
  · refine ⟨by simp [H1, List.getElem?_set, hrbl]; rfl, by simp; omega, h3, by simp [H1]; omega, fun k' hk' => ?_⟩
    simp only [Array.size_push] at hk'
    by_cases e : k' = k
    · subst e
      refine ⟨r, ?_, ?_⟩
      · show ((H.set (rb + 1 + k) (cellA C r)).set rb (BitVec.ofNat 64 (k + 1)))[rb + 1 + k]? = _
        rw [List.getElem?_set, if_neg (by omega), List.getElem?_set, if_pos rfl, if_pos (by omega)]
      · simp only [k, Array.getElem_push_eq]
        exact recEnc_set (recEnc_set hrec _ (by omega) _) _ (by omega) _
    · obtain ⟨o, ho, hro⟩ := h5 k' (by omega)
      refine ⟨o, ?_, ?_⟩
      · show ((H.set (rb + 1 + k) (cellA C r)).set rb (BitVec.ofNat 64 (k + 1)))[rb + 1 + k']? = _
        rw [List.getElem?_set, if_neg (by omega), List.getElem?_set, if_neg (by omega)]; exact ho
      · rw [Array.getElem_push_lt (by omega)]
        exact recEnc_set (recEnc_set hro _ (by omega) _) _ (by omega) _

end ConPanqueque.Front
