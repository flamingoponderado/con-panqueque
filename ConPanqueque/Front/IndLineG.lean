import ConPanqueque.Front.IndLineF

/-! # The inductive line: the recursor, the block and the record

`recP`: the recursor record (`ilRq`): its name (viewable), type and level parameters (`cvP`), its counts
against the block (`numParams` the type's, one motive, a minor per constructor), its index count
against the type's sort telescope (hang on a mismatch), `k`, its rules (`indRuleLoop`), its stored
constant `[5, name, lps, type, mi, rp, k, rules]` in the last slot of the pointer block; then the
declaration record `[4, nP, block]` and the registry push. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec IndTypeRec IndCtorRec IndRecRec RuleRec scanRules scanRule scanIndRec)

set_option autoImplicit false

variable {σ : Type}

def ilRq := ofString "il_rq"
def ilTy := ofString "il_ty"
def ilD := ofString "il_d"
def ilK := ofString "il_k"

def b56W : BitVec 64 := BitVec.ofNat 64 (2 ^ 56)

def recRules (C : Ctx) : ProgHOL 64 :=
  .seq (callTo ilK (fIrF 1) [vv kBA, vv kBN, vv ilRq])
  (.seq (callTo ilRl (fIrF 8) [vv kBA, vv kBN, vv ilRq])
  (.seq (callTo ilNu fRulesN [vv kBA, vv kBN, vv ilRl])
  (.ite (.cmp .lower (vv ilNu) (.const b55W))
    (allocP C ilRP (.shift .lsl (.op .add [vv ilNu, .const 1]) (.const 3))
    (.seq (.store (vv ilRP) (vv ilNu))
    (.seq (.call (some (some (.local, ilZ), none)) fRuleLoop (ruleArgs (.const 0)))
    (.seq (.assign .local ilA (.op .add [.op .add [vv ilP, .const 1], vv ilNc]))
    (.seq (.assign .local ilB (.op .add [vv ilA, vv ilD]))
    (.ite (.cmp .lower (vv ilB) (.const b56W))
    (allocWr C ilR [.const 5, vv fy, vv kKA0, vv fz, vv ilB, vv ilA, vv ilK, vv ilRP]
    (.seq (.store (slotE ilOB ilNc 2) (vv ilR))
    (allocWr C kR [.const 4, vv ilP, vv ilOB] regPushP))) hang)))))) hang)))

def recP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fU (fIrF 3) [vv kBA, vv kBN, vv ilRq])
  (.seq (callTo fW3 (fIrF 9) [vv kBA, vv kBN, vv ilRq])
  (.seq (callTo fV2 (fIrF 2) [vv kBA, vv kBN, vv ilRq])
  (cvP C
  (.seq (.call (some (some (.local, ilX), none)) T.Ind.fNvChk [vv fy])
  (.seq (callTo ilA (fIrF 7) [vv kBA, vv kBN, vv ilRq])
  (.ite (.cmp .notEqual (vv ilA) (vv ilP)) hang
  (.seq (callTo ilA (fIrF 6) [vv kBA, vv kBN, vv ilRq])
  (.ite (.cmp .notEqual (vv ilA) (.const 1)) hang
  (.seq (callTo ilA (fIrF 5) [vv kBA, vv kBN, vv ilRq])
  (.ite (.cmp .notEqual (vv ilA) (vv ilNc)) hang
  (.seq (callTo ilD (fIrF 4) [vv kBA, vv kBN, vv ilRq])
  (.ite (.cmp .lower (vv ilD) (.const b55W))
    (.seq (.call (some (some (.local, ilX), none)) T.Ind.fPiSortTele [.const b55W, vv ilTy])
    (.seq (.assign .local ilY (.op .add [.op .add [vv ilP, vv ilD], .const 1]))
    (.ite (.op .and [.cmp .notEqual (vv ilX) (.const 0), .cmp .notEqual (vv ilX) (vv ilY)]) hang
      (recRules C))))
    hang))))))))))))

def recMods : List MlS := [fU, fW3, fV2, ilX, ilA, ilD, ilY, ilK, ilRl, ilNu, ilRP, ilZ, ilB, ilR, kR, kCnt] ++ cvMods

/-- The recursor's twin facts (and bounds). -/
structure RecTwin (st : StateD) (s : AState) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (tyh : EIdx) :
    Prop where
  rn : ∃ rn, st.names.get? r.cv.name = some rn ∧ (s.store.ns.view rn).isSome = true
  rp : r.numParams = t.numParams
  rm : r.numMotives = 1
  rmin : r.numMinors = cts.length
  idx : ∃ o, piSortTeleLen? (s.store.nodeCount + 1) tyh s = .ok (o, s) ∧ ∀ n, o = some n → t.numParams + r.numIndices = n
  rules : ∀ ru ∈ r.rules, (st.names.get? ru.ctor).isSome ∧ (st.exprs.get? ru.rhs).isSome
  lps : ∀ x ∈ r.cv.levelParams, (st.names.get? x).isSome
  ni : r.numIndices < B55
  nr : r.rules.length < B55
  nf : ∀ ru ∈ r.rules, ru.nfields < B55
  lpl : r.cv.levelParams.length < B55
  tele : ∃ rty n, st.exprs.get? r.cv.type = some rty ∧ n < B55 ∧
    ∀ e, denoteE s.store rty = some e → n = ConLeche.Frontend.indPiTeleLen e
  mi : r.numParams + r.numMotives + r.numMinors + r.numIndices < 2 ^ 56

/-- The type former and the constructors of the block. -/
def indHead (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (T : NIdx) : List IConstantInfo :=
  [.indInfo (cvOfD st t.cv) {}] ++ cts.map (fun c => .ctorInfo (cvOfD st c.cv) c.numParams c.numFields T)

def recInfoD (st : StateD) (r : IndRecRec) : IConstantInfo :=
  .recInfo (cvOfD st r.cv) (r.numParams + r.numMotives + r.numMinors + r.numIndices)
    (r.numParams + r.numMotives + r.numMinors) r.k (r.rules.map (ruleOfD st))

theorem indBlockD_eq (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx) :
    indBlockD st t cts r T = indHead st t cts T ++ [recInfoD st r] := rfl

theorem indHead_length (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (T : NIdx) :
    (indHead st t cts T).length = cts.length + 1 := by simp [indHead]

end ConPanqueque.Front

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec IndTypeRec IndCtorRec IndRecRec RuleRec scanRules scanRule scanIndRec)

set_option autoImplicit false

variable {σ : Type}

theorem bw_boolW (k : Bool) : bw (k = true) = boolW k := by cases k <;> rfl

theorem rrule_mono {X Y : Nat} {C : Ctx} {H : List (BitVec 64)} {o : Nat} {ru : IRecRule}
    (h : RRule Y C H o ru) (hXY : X ≤ Y) : RRule X C H o ru :=
  fun H' hk => h H' (keepsAbove_mono hk hXY)

theorem keepsAbove_set_ne {X : Nat} {H : List (BitVec 64)} {c : Nat} (hc : c < X) (w : BitVec 64) :
    KeepsAbove X H (H.set c w) := keepsAbove_set_lt hc w

theorem get_set_ne' {H : List (BitVec 64)} {c d : Nat} {v w : BitVec 64} (h : H[c]? = some v) (hne : c ≠ d) :
    (H.set d w)[c]? = some v := by
  rw [List.getElem?_set, ite_eq_right (by omega)]; exact h

/-- The block's encoding at the final image, from the head's at `H`, the recursor's, and the slot. -/
theorem indBlk_final (C0 : Ctx) (F : Nat) (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx)
    (H Hf : List (BitVec 64)) (ob oR : Nat) (os : List Nat) (hosl : os.length = cts.length + 1)
    (hob0 : Hf[ob]? = some (BitVec.ofNat 64 (cts.length + 2)))
    (hos : ∀ i (hi : i < os.length), Hf[ob + 1 + i]? = some (cellA C0 os[i]))
    (hslot : Hf[ob + 2 + cts.length]? = some (cellA C0 oR))
    (hhead : ∀ i (hi : i < (indHead st t cts T).length) (ho : i < os.length),
      RCIE (ob + cts.length + 3) C0 Hf os[i] (indHead st t cts T)[i])
    (hrec : RCIE (ob + cts.length + 3) C0 Hf oR (recInfoD st r)) (hF : F ≤ ob) :
    ∀ H', KeepsAbove F Hf H' → ConPanqueque.T.Ind.IndBlk C0 H' ob (indBlockD st t cts r T) := by
  intro H' hk
  rw [indBlockD_eq]
  have hl : (os ++ [oR]).length = (indHead st t cts T ++ [recInfoD st r]).length := by
    simp [indHead_length, hosl]
  have hkX : KeepsAbove (ob + cts.length + 3) Hf H' := keepsAbove_mono hk (by omega)
  refine ⟨os ++ [oR], hl, blkAt_keep hk ⟨by simpa [hosl] using hob0, fun i hi => ?_⟩ hF, fun i hi ho => ?_⟩
  · simp only [List.length_map, List.length_append, List.length_singleton, hosl] at hi
    by_cases e : i < os.length
    · simp only [List.getElem_map, List.getElem_append_left e]; exact hos i e
    · have : i = os.length := by omega
      subst this
      simp only [List.getElem_map, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_singleton]
      rw [show ob + 1 + os.length = ob + 2 + cts.length by omega]; exact hslot
  · by_cases e : i < os.length
    · rw [List.getElem_append_left e, List.getElem_append_left (by rw [indHead_length]; omega)]
      exact hhead i (by rw [indHead_length]; omega) e H' hkX
    · have h1 : i = os.length := by simp at ho; omega
      subst h1
      rw [List.getElem_append_right (Nat.le_refl _),
        List.getElem_append_right (by rw [indHead_length]; omega)]
      simp only [Nat.sub_self, List.getElem_singleton]
      first
        | exact hrec H' hkX
        | (rw [show os.length - (indHead st t cts T).length = 0 by rw [indHead_length]; omega]; exact hrec H' hkX)


theorem indBlock_lps (st : StateD) (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx)
    (hlpT : t.cv.levelParams.length < B55) (hlpC : ∀ c ∈ cts, c.cv.levelParams.length < B55)
    (hlpR : r.cv.levelParams.length < B55) :
    ∀ ci ∈ indBlockD st t cts r T, ci.toConstantVal.levelParams.length < B55 := by
  intro ci hci
  simp only [indBlockD, List.mem_append, List.mem_singleton, List.mem_map] at hci
  rcases hci with (rfl | ⟨c, hc, rfl⟩) | rfl
  · simp only [IConstantInfo.toConstantVal, cvOfD, List.length_map]; exact hlpT
  · simp only [IConstantInfo.toConstantVal, cvOfD, List.length_map]; exact hlpC c hc
  · simp only [IConstantInfo.toConstantVal, cvOfD, List.length_map]; exact hlpR

theorem recRules_spec {α : Type} (C0 : Ctx) (hok : CtxOK C0) (cc : ILCodes σ C0)
    (hrL : C0.code.lookup fRuleLoop = some (rulePs.map (fun p => (p, ShapeHOL.one)), prologue ruleL (ruleCore C0), .one))
    (s : AState) (Γ : Env) (D : List MlS) (hD : ∀ x ∈ recMods, x ∈ D)
    (st : StateD) (F rb capD jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C0.H jN cap st.names) (hrele : TblRel C0.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C0 bufJ b)
    (hdr : DeclsRel C0 F rb capD C0.H st.decls) (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (t : IndTypeRec) (cts : List IndCtorRec) (r : IndRecRec) (T : NIdx) (qR eR : USize) (hqR : qR.toNat ≤ b.size)
    (hsR : scanIndRec b qR = .ok r eR)
    (hnP : t.numParams < B55) (hnC : cts.length < B55) (hrp : r.numParams = t.numParams) (hrm : r.numMotives = 1)
    (hrmin : r.numMinors = cts.length) (hni : r.numIndices < B55)
    (hlpT : t.cv.levelParams.length < B55) (hlpC : ∀ c ∈ cts, c.cv.levelParams.length < B55)
    (hlpR : r.cv.levelParams.length < B55)
    (H Hc : List (BitVec 64)) (hp0 : C0.H <+: H) (hpc : H <+: Hc) (ob : Nat) (hob : C0.H.length ≤ ob)
    (hX : ob + cts.length + 3 ≤ H.length)
    (hob0 : H[ob]? = some (BitVec.ofNat 64 (cts.length + 2))) (os : List Nat) (hosl : os.length = cts.length + 1)
    (hos : ∀ i (hi : i < os.length), H[ob + 1 + i]? = some (cellA C0 os[i]))
    (hhead : ∀ i (hi : i < (indHead st t cts T).length) (ho : i < os.length),
      RCIE (ob + cts.length + 3) C0 H os[i] (indHead st t cts T)[i])
    (rn : NIdx) (rty : EIdx) (hrn : st.names.get? r.cv.name = some rn) (hrty : st.exprs.get? r.cv.type = some rty)
    (ol : Nat) (hol : H.length ≤ ol) (hblk : BlkAt Hc ol (tWords st.names r.cv.levelParams))
    (hBA : Γ.get kBA = some (cellA C0 bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hTN : Γ.get fTN = some (cellA C0 jN)) (hTE : Γ.get fTE = some (cellA C0 jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hRB : Γ.get kRB = some (cellA C0 rb))
    (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hRq : Γ.get ilRq = some (BitVec.ofNat 64 qR.toNat)) (hP : Γ.get ilP = some (BitVec.ofNat 64 t.numParams))
    (hNc : Γ.get ilNc = some (BitVec.ofNat 64 cts.length)) (hOB : Γ.get ilOB = some (cellA C0 ob))
    (hDd : Γ.get ilD = some (BitVec.ofNat 64 r.numIndices))
    (hy : Γ.get fy = some (Enc.idxW rn)) (hz : Γ.get fz = some (Enc.idxW rty)) (hK0 : Γ.get kKA0 = some (cellA C0 ol))
    (hfd : (∀ ru ∈ r.rules, RuleOK st ru) → r.rules.length < B55 →
      r.numParams + r.numMotives + r.numMinors + r.numIndices < 2 ^ 56 → IndBoundsP (indBlockD st t cts r T) t.numParams)
    {m : AM (StateD ⊕ RecordVerdict)}
    (hm : (∀ ru ∈ r.rules, RuleOK st ru) → r.rules.length < B55 →
      r.numParams + r.numMotives + r.numMinors + r.numIndices < 2 ^ 56 →
      m s = (pure (.inl { st with decls := st.decls.push (.indDecl (indBlockD st t cts r T) t.numParams) }) :
        AM (StateD ⊕ RecordVerdict)) s) :
    SpecR (Inv (σ := σ) (ctxH C0 Hc) s Γ [] D) (recRules C0) s m
      (fun a w s' t' => DeclPost C0 F rb capD C0.H st (.indDecl (indBlockD st t cts r T) t.numParams) a w s' t' ∧
        (∀ ru ∈ r.rules, RuleOK st ru) ∧ r.rules.length < B55 ∧
        r.numParams + r.numMotives + r.numMinors + r.numIndices < 2 ^ 56) := by
  have hplat := hbuf.plat
  have hpc0 : C0.H <+: Hc := hp0.trans hpc
  have hokc := ctxOK_H hok Hc
  have hbufc := bufOK_prefix hbuf hpc0
  have hlay := hok.heapLay
  have hFl : F ≤ C0.H.length := hdr.2.2.2.1
  unfold recRules
  refine specR_scan3 hokc bufJ b hbufc ilK (fIrF 1) ilRq _ qR.toNat _ (hD ilK (by simp [recMods])) (cc.recF 1 (by decide))
    hBA hBN hRq
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 1 (by decide) _ eR hsR)
    (fun wk hwk => ?_)
  simp only [IndRecField] at hwk; subst hwk
  refine specR_scan3 hokc bufJ b hbufc ilRl (fIrF 8) ilRq _ qR.toNat _ (hD ilRl (by simp [recMods])) (cc.recF 8 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg; exact hRq)
    (fun u hb hu l1 l2 l3 => indRecField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) qR hqR l1 l2 l3 8 (by decide) _ eR hsR)
    (fun wl hwl => ?_)
  simp only [IndRecField] at hwl
  obtain ⟨pR, eRu, rfl, hpR⟩ := hwl
  have hpRb : pR.toNat ≤ b.size := Nat.le_of_lt (objListOpen_pos hplat (by rw [← scanRules_objList]; exact hpR))
  refine specR_scan3 hokc bufJ b hbufc ilNu fRulesN ilRl _ pR.toNat _ (hD ilNu (by simp [recMods])) cc.rulesN
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => ruleCount_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pR eRu r.rules hpR l1 l2 l3)
    (fun wn ⟨hwn, hnb⟩ => ?_)
  subst hwn
  refine specR_ltGuardI ilNu (BitVec.ofNat 64 r.rules.length) b55W (by envg) (fun hlu => ?_)
  have hnU : r.rules.length < B55 := lt_b55 rfl (by have := hbuf.small; omega) hlu
  have hsm := hbuf.small
  unfold B55 at hnU hnP hnC hni
  -- the rule block
  let Γ3 : Env := (ilNu, BitVec.ofNat 64 r.rules.length) :: (ilRl, BitVec.ofNat 64 pR.toNat) ::
    (ilK, bw (r.k = true)) :: Γ
  refine specR_allocI (C := ctxH C0 Hc) ilRP (.shift .lsl (.op .add [vv ilNu, .const 1]) (.const 3)) (r.rules.length + 1)
    (by omega) (hD ilRP (by simp [recMods])) (fun v => by
      simp only [sev, vv, ConPanqueque.T.Env.get_cons, show (ilNu = ilRP) = False from by decide, ite_false,
        ite_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
        show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]; omega)
    (fun H4 wsR hp4 hwl hcap4 => ?_)
  have hcH4 : Hc.length ≤ H4.length := hp4.length_le
  let rp := H4.length
  refine specR_heapStoreI (C := ctxH C0 (H4 ++ wsR)) (ctxOK_H hok _) (vv ilRP) (vv ilNu) rp
    (by show H4.length < (H4 ++ wsR).length; simp [hwl]) (BitVec.ofNat 64 r.rules.length) (by simp [sev, vv, ConPanqueque.T.Env.get_cons]; rfl)
    (by simp [sev, vv, ConPanqueque.T.Env.get_cons, show ilNu ≠ ilRP from by decide]) ?_
  let H4' := (H4 ++ wsR).set rp (BitVec.ofNat 64 r.rules.length)
  have hl4' : H4'.length = H4.length + (r.rules.length + 1) := by simp [H4', hwl]
  have hp4' : Hc <+: H4' := prefix_set_ge (hp4.trans (List.prefix_append _ _)) rp (by show Hc.length ≤ H4.length; omega) _
  have hrp4 : H4'[rp]? = some (BitVec.ofNat 64 r.rules.length) := by simp [H4', List.getElem?_set, hwl, rp]
  -- the rules
  let Γ4 : Env := (ilRP, cellA C0 rp) :: Γ3
  have g4 : ∀ y, y ∉ [ilRP, ilNu, ilRl, ilK] → Γ4.get y = Γ.get y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Γ4, Γ3, ConPanqueque.T.Env.get_cons, ite_eq_right hy.1, ite_eq_right hy.2.1, ite_eq_right hy.2.2.1,
      ite_eq_right hy.2.2.2]
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => m) rfl ?_
  refine specR_protoCall (C := ctxH C0 H4') ilZ fRuleLoop rulePs (by decide) ruleL (ruleCore C0) (ruleArgs (.const 0))
    (ruleVals (ctxH C0 H4') bufJ b.size jN jE cap pR.toNat 0 r.rules.length rp) rfl (hD ilZ (by simp [recMods])) hrL ?_
    (ruleL_none (ctxH C0 H4') bufJ b.size jN jE cap pR.toNat 0 r.rules.length rp)
    (RulePost (ctxH C0 H4') s st r.rules rp (rp + r.rules.length + 1) 0)
    (fun _ _ _ _ _ ⟨h0, H'', h1, h2⟩ => ⟨h0, H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
    (ruleCore_spec C0 hok cc hrL s st jN jE cap bufJ b hreln hrele hcap hcapN hbuf r.rules pR eRu hpR hnU rp
      (by have := hpc0.length_le; omega) r.rules.length 0 H4' (by omega) (Nat.zero_le _) (hpc0.trans hp4') (by omega))
    (fun _ _ s'' H'' => s'' = s ∧ RuleFacts (ctxH C0 H4') st r.rules rp (rp + r.rules.length + 1) 0 H'')
    (fun a w s'' u ⟨h0, H'', h1, h2⟩ => ⟨H'', ⟨h0, h2⟩, by rw [h0]; exact h1⟩) ?_
  · simp only [EvAll, ruleArgs, ruleVals, sev, vv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, trivial⟩
    · exact (g4 kBA (by decide)).trans hBA
    · exact (g4 kBN (by decide)).trans hBN
    · exact (g4 fTN (by decide)).trans hTN
    · exact (g4 fTE (by decide)).trans hTE
    · exact (g4 fCap (by decide)).trans hC
    · envg
    · envg
    · envg; rfl
  intro a w s'' H5 ⟨h0, hl5, hpres5, hall5⟩
  subst s''
  have hl5' : H4'.length ≤ H5.length := hl5
  have hpres5' : ∀ c v, H4'[c]? = some v → (c < rp + 1 + 0 ∨ rp + r.rules.length + 1 ≤ c) → H5[c]? = some v := hpres5
  have hp5 : Hc <+: H5 := prefix_of_agree (by omega) (fun c hc => by
    obtain ⟨v, hv⟩ : ∃ v, Hc[c]? = some v := ⟨Hc[c], List.getElem?_eq_getElem hc⟩
    rw [hv, hpres5' c v (getElem?_prefix hp4' hv) (by omega)])
  have hrp5 : H5[rp]? = some (BitVec.ofNat 64 r.rules.length) := hpres5' _ _ hrp4 (by omega)
  -- the rule pointers
  let ors : List Nat := List.ofFn (fun j : Fin r.rules.length => Classical.choose (hall5 j.1 (Nat.zero_le _) j.2))
  have hors : ∀ j (hj : j < r.rules.length) (ho : j < ors.length), rp + r.rules.length + 1 ≤ ors[j] ∧
      H5[rp + 1 + j]? = some (cellA C0 ors[j]) ∧
      RRule (rp + r.rules.length + 1) C0 H5 ors[j] (ruleOfD st r.rules[j]) ∧ RuleOK st r.rules[j] := by
    intro j hj ho
    have := Classical.choose_spec (hall5 j (Nat.zero_le _) hj)
    simp only [ors, List.getElem_ofFn]
    exact this
  have horsl : ors.length = r.rules.length := by simp [ors]
  have hrok : ∀ ru ∈ r.rules, RuleOK st ru := fun ru hru => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hru
    rw [← e]; exact (hors j hj (by omega)).2.2.2
  -- counts into the recursor's record
  let Γ5 : Env := (ilZ, w) :: Γ4
  have g5 : ∀ y, y ∉ [ilZ, ilRP, ilNu, ilRl, ilK] → Γ5.get y = Γ.get y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Γ5, ConPanqueque.T.Env.get_cons, ite_eq_right hy.1]
    exact g4 y (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hy.2)
  refine specR_assignI ilA (.op .add [.op .add [vv ilP, .const 1], vv ilNc])
    (BitVec.ofNat 64 (t.numParams + 1 + cts.length)) (hD ilA (by simp [recMods])) (by
      simp only [sev, vv, Γ5, Γ4, Γ3]; envg; rw [hP, hNc]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  refine specR_assignI ilB (.op .add [vv ilA, vv ilD])
    (BitVec.ofNat 64 (t.numParams + 1 + cts.length + r.numIndices)) (hD ilB (by simp [recMods])) (by
      simp only [sev, vv]; envg; rw [hDd]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  refine specR_ltGuardI ilB (BitVec.ofNat 64 (t.numParams + 1 + cts.length + r.numIndices)) b56W (by envg)
    (fun hlB => ?_)
  -- the recursor's record
  have hcvR := cvOfD_eq st r.cv rn rty hrn hrty
  have hmi : r.numParams + r.numMotives + r.numMinors + r.numIndices = t.numParams + 1 + cts.length + r.numIndices := by
    rw [hrp, hrm, hrmin]
  have hmi56 : r.numParams + r.numMotives + r.numMinors + r.numIndices < 2 ^ 56 := by
    rw [hmi]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlB
    exact hlB
  have hrp' : r.numParams + r.numMotives + r.numMinors = t.numParams + 1 + cts.length := by rw [hrp, hrm, hrmin]
  refine specR_allocWrI (ctxH C0 H5) (ctxOK_H hok H5) ilR (hD ilR (by simp [recMods]))
    [.const 5, vv fy, vv kKA0, vv fz, vv ilB, vv ilA, vv ilK, vv ilRP]
    [BitVec.ofNat 64 5, Enc.idxW rn, cellA C0 ol, Enc.idxW rty, BitVec.ofNat 64 (t.numParams + 1 + cts.length + r.numIndices),
      BitVec.ofNat 64 (t.numParams + 1 + cts.length), bw (r.k = true), cellA C0 rp] rfl (by simp)
    (fun v i hi => ?_) (fun H6 oR hp6 hr6 hlen6 hw6 => ?_)
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero, sev, vv] <;>
    envg
    · exact hy
    · exact hK0
    · exact hz
    · rfl
  have hl6 : H5.length ≤ H6.length := hp6.length_le
  have hr6' : H5.length ≤ oR := hr6
  have hcH5 : Hc.length ≤ H5.length := hp5.length_le
  have hHc : H.length ≤ Hc.length := hpc.length_le
  have hslot6 : ob + 2 + cts.length < H6.length := by omega
  refine specR_heapStoreI (C := ctxH (ctxH C0 H5) H6) (ctxOK_H hok H6) (slotE ilOB ilNc 2) (vv ilR)
    (ob + 2 + cts.length) (by show ob + 2 + cts.length < H6.length; omega) (cellA C0 oR)
    (sev_slot _ (ctxH (ctxH C0 H5) H6) ilOB ilNc ob cts.length 2 (by envg; exact hOB) (by envg; exact hNc) (by omega))
    (by simp only [sev, vv, ConPanqueque.T.Env.get_cons, ite_true] <;> rfl) ?_
  let H7 := H6.set (ob + 2 + cts.length) (cellA C0 oR)
  have hl7 : H7.length = H6.length := by simp [H7]
  have hp7 : C0.H <+: H7 := prefix_set_ge (hpc0.trans (hp5.trans hp6)) _ (by have := hpc0.length_le; omega) _
  refine specR_allocWrI (ctxH C0 H7) (ctxOK_H hok H7) kR (hD kR (by simp [recMods]))
    [.const 4, vv ilP, vv ilOB] [BitVec.ofNat 64 4, BitVec.ofNat 64 t.numParams, cellA C0 ob] rfl (by simp)
    (fun v i hi => ?_) (fun H8 r0 hp8 hr8 hlen8 hw8 => ?_)
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero, sev, vv] <;>
    envg
    · exact hP
    · exact hOB
  have hr8' : H7.length ≤ r0 := hr8
  have hp08 : C0.H <+: H8 := hp7.trans hp8
  have hnU' : r.rules.length < B55 := by unfold B55; omega
  refine specR_congr (hm hrok hnU' hmi56) ?_
  -- the record's encoding
  have tr : ∀ c v, H[c]? = some v → c ≠ ob + 2 + cts.length → H8[c]? = some v := fun c v hv hne =>
    getElem?_prefix hp8 (get_set_ne' (getElem?_prefix (hpc.trans (hp5.trans hp6)) hv) hne)
  have kX : KeepsAbove (ob + cts.length + 3) H6 H8 := fun c hc v hv =>
    getElem?_prefix hp8 (get_set_ne' hv (by omega))
  have hrecR : RCIE (ob + cts.length + 3) C0 H6 oR (recInfoD st r) := by
    unfold recInfoD
    refine rcie_rec _ C0 H6 oR ol rp (cvOfD st r.cv) _ _ r.k (r.rules.map (ruleOfD st)) ors (by omega) (by omega)
      (by show ob + cts.length + 3 ≤ H4.length; omega) (by rw [hmi]; omega) (by rw [hrp']; omega)
      (fun i hi => ?_) ?_ (by simp [horsl]) ⟨?_, fun i hi => ?_⟩ (fun i hi ho => ?_)
    · rw [hcvR, hmi, hrp', ← bw_boolW]; have := hw6 i (by simpa using hi); simpa using this
    · rw [tWords_cvOfD]; exact blkAt_mono hblk (hp5.trans hp6)
    · simpa [horsl] using getElem?_prefix hp6 hrp5
    · simp only [List.length_map] at hi
      have := (hors i (by omega) hi).2.1
      simpa using getElem?_prefix hp6 this
    · have := (hors i (by simpa using hi) ho).2.2.1
      simpa using rrule_keep (rrule_mono this (by show ob + cts.length + 3 ≤ H4.length + r.rules.length + 1; omega))
        (keepsAbove_prefix hp6)
  refine specR_mono (regPush_spec C0 hok s _ D (hD kCnt (by simp [recMods])) F rb capD C0.H H8 st
    (.indDecl (indBlockD st t cts r T) t.numParams) r0
    (fun c hc _ => by obtain ⟨q, hq⟩ := hp08; rw [← hq, List.getElem?_append_left (by omega)])
    hp08.length_le (declsRel_prefix hdr hp08) ?_ hcapD
    (by envg; exact hRB) (by envg; exact hCD) (by envg <;> rfl)) (fun u hu => hu) (fun a w s' u h => ⟨h, hrok, hnU', hmi56⟩)
  have hFob : F ≤ ob := by omega
  refine ⟨hfd hrok hnU' hmi56, by omega, by simpa using hw8 0 (by simp), by simpa using hw8 1 (by simp), ob, hFob,
    by simpa using hw8 2 (by simp), ?_, by simp [indBlockD]; omega, by omega, fun i hi => ?_⟩
  · intro H' hk'
    exact indBlk_final C0 F st t cts r T H H8 ob oR os hosl (tr _ _ hob0 (by omega))
      (fun i hi => tr _ _ (hos i hi) (by omega)) (getElem?_prefix hp8 (by show H7[ob + 2 + cts.length]? = _; simp [H7, List.getElem?_set, hslot6]))
      (fun i hi ho => rcie_keep (hhead i hi ho) (fun c hc v hv => tr c v hv (by omega)))
      (rcie_keep hrecR kX) hFob H' (fun c hc v hv => hk' c hc v (getElem?_prefix (List.prefix_refl _) hv))
  · have := indBlock_lps st t cts r T hlpT hlpC hlpR _ (List.getElem_mem hi)
    unfold B55 at this; omega

end ConPanqueque.Front
