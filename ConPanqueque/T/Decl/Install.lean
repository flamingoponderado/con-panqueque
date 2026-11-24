import ConPanqueque.T.Decl.Push
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Installing a checked constant

`fe.push ci` in the port: the constant's block is already in the environment heap (copied), its name goes into
the constant table, and the context becomes `ctxPush C ci o EH`. A call may end in another context than it
started in (the table it writes is part of the context), so the call and table-set lemmas here are stated across
two contexts.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The context after installing `ci` at environment block `o` of image `EH`. -/
def ctxPush (C : Ctx) (ci : IConstantInfo) (o : Nat) (EH : List (BitVec 64)) : Ctx :=
  { C with fe := C.fe.push ci, EH := EH, envM := C.envM.insert ci.name (ecell C o) }

theorem envRel_push {C : Ctx} (h : EnvRel C) (hg : TblGate C.fe) {ci : IConstantInfo} {o : Nat}
    {EH : List (BitVec 64)} (hp : C.EH <+: EH) (hcie : CIE C.EB EH o ci) (hnew : C.fe.find? ci.name = none) :
    EnvRel (ctxPush C ci o EH) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · show match (C.fe.push ci).find? n with
      | none => (C.envM.insert ci.name (ecell C o))[n]? = none
      | some ci' => ∃ o', (C.envM.insert ci.name (ecell C o))[n]? = some (ecell C o') ∧ CIE C.EB EH o' ci'
    rw [IFEnv.find?_push, Std.HashMap.getElem?_insert]
    by_cases e : (ci.name == n) = true
    · simp only [e, if_true]; exact ⟨o, rfl, hcie⟩
    · have ef : (ci.name == n) = false := by simpa using e
      simp only [ef, Bool.false_eq_true, if_false]
      have := h.1 n
      revert this
      cases C.fe.find? n with
      | none => exact id
      | some ci' => exact fun ⟨o', hm, hc⟩ => ⟨o', hm, cie_mono hp hc⟩
  · show match (C.fe.push ci).findTable? n with
      | none => C.tblM[n]? = none
      | some tb => ∃ o', C.tblM[n]? = some (ecell C o') ∧ TblE C.EB EH o' tb
    rw [push_findTable hg ci hnew]
    have := h.2 n
    revert this
    cases C.fe.findTable? n with
    | none => exact id
    | some tb => exact fun ⟨o', hm, hc⟩ => ⟨o', hm, tblE_mono hp hc⟩

theorem ctxOK_push {C : Ctx} (hok : CtxOK C) (hg : TblGate C.fe) {ci : IConstantInfo} {o : Nat}
    {EH : List (BitVec 64)} (hp : C.EH <+: EH) (hcie : CIE C.EB EH o ci) (hnew : C.fe.find? ci.name = none) :
    CtxOK (ctxPush C ci o EH) := by
  have h1 := envRel_push hok.envRel hg hp hcie hnew
  have h2 : PinsE (ctxPush C ci o EH) := pinsE_E hok.pinsRel hp
  cases hok; constructor <;> first | assumption | exact h1 | exact h2

section
variable {σ : Type}

/-- A three-argument call that ends in another context `C'` (its post builds `SR C'`). -/
theorem specR_call3IMC {α β : Type} {C C' : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 p3 : MlS) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (e1 e2 e3 : ExpHOL 64) (B : ProgHOL 64)
    (v1 v2 v3 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one), (p3, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2) (he3 : sev Γ e3 = some v3)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C' s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) → u.locals.lookup p2 = some (.val (.word v2)) →
      u.locals.lookup p3 = some (.val (.word v3)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C' s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2, e3]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call3 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C' s' ((x, w) :: Γ) [] D t')
    x f p1 p2 p3 h12 h13 h23 e1 e2 e3 B (fun _ => v1) (fun _ => v2) (fun _ => v3)
    (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact inv_ev ht he3)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 h3 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2 h3)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C' s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

end


section
variable {σ : Type} {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
  {enc : K → List (BitVec 64)} {valW : V → BitVec 64}

/-- `specR_memoSetGI`, ending in another context `C'` (the table set is part of the context). -/
theorem specR_memoSetGIC {β : Type} {C C' : Ctx} (hinj : ∀ x y, enc x = enc y → x = y)
    (G : BitVec 64) (g : VGeo) (m : Std.HashMap K V) (key : K) (v : V) (setOp : AM Unit) {s s' : AState}
    (hset : setOp s = .ok ((), s'))
    (hmem : ∀ u : PState σ, SR C s u → MemoAtG enc valW u G g m)
    (hKout : ∀ i, i < (enc key).length → ¬ inR g (C.KB + BitVec.ofNat 64 (8 * i)))
    (hGout : ∀ j, j < 8 → ¬ inR g (G + BitVec.ofNat 64 (8 * j)))
    (hsr' : ∀ u u' : PState σ, SR C s u → MemoAtG enc valW u' G g (m.insert key v) →
      (∀ c, ¬ inR g c → u'.memory c = u.memory c) → u'.memaddrs = u.memaddrs → u'.globals = u.globals →
      u'.code = u.code → SR C' s' u')
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eG eL ev : ExpHOL 64) (hx : x ∈ D) (heG : sev Γ eG = some G)
    (heL : sev Γ eL = some (BitVec.ofNat 64 (enc key).length)) (hev : sev Γ ev = some (valW v))
    (hkl : (enc key).length < 2 ^ 61)
    (hW : ∀ u : PState σ, (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) → Words u C.KB (enc key))
    (hk : ∀ w, SpecR (Inv C' s' ((x, w) :: Γ) [] D) rest s' (k ()) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fMemoSet [eG, eL, ev]) rest) s
      (setOp >>= k) R := by
  refine specR_call3IMC (C' := C') x fMemoSet pG pLen pVal (by decide) (by decide) (by decide) eG eL ev memoSetBody G
    (BitVec.ofNat 64 (enc key).length) (valW v) hx hcodeS heG heL hev
    (fun _ _ s'' st => s'' = s' ∧ SR C' s' st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2)
    (fun u hsr hM h1 h2 h3 => ?_) (fun a w s'' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk w)
  have S := memoSet_spec (σ := σ) G C.KB g hinj m key v s u (hmem u hsr) (hW u hM) hkl hKout hGout hsr.gkb h1 h2 h3
    (by rw [hsr.code]; exact hcodeI)
  intro t ht
  rcases S t ht with hs | ⟨w, hr', _, s'', _, hp⟩
  · exact Or.inl hs
  obtain ⟨_, hmem', hfr, hd', hg, hc⟩ := hp
  subst ht
  exact Or.inr ⟨w, hr', (), s', hset, rfl, hsr' t _ hsr hmem' hfr hd' hg hc⟩

end


/-- A context with the environment `fe`, image `EH` and constant table `envM` in place of `C`'s. -/
def ctxIns (C : Ctx) (fe : IFEnv) (EH : List (BitVec 64)) (envM : Std.HashMap NIdx (BitVec 64)) : Ctx :=
  { C with fe := fe, EH := EH, envM := envM }

section
variable {σ : Type}

/-- Rebuilding `SR` after a write confined to the constant table's region: every other part is framed; the
caller supplies the new table, the environment's denotation facts, and the unchanged literal word. -/
theorem sr_envIns {C : Ctx} {EH : List (BitVec 64)} (hok : CtxOK (ctxE C EH)) {s : AState} {t u : PState σ}
    (hsr : SR (ctxE C EH) s t) (hfr : ∀ c, ¬ inR (C.mg .env) c → u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals = t.globals) (hc : u.code = t.code)
    {fe : IFEnv} {envM : Std.HashMap NIdx (BitVec 64)}
    (hm : MemoAtG encNI id u (C.mG .env) (C.mg .env) envM) (hlit : litW fe = litW C.fe)
    (hden : EnvDen fe C.pins s.store) :
    SR (ctxIns C fe EH envM) s u := by
  have r := Region.env
  obtain ⟨hH, _, hm2, hl⟩ := hsr.env
  refine ⟨srep_frame hsr.rep ⟨hfr _ (hok.flMemo .env _ (Or.inl rfl)), hfr _ (hok.flMemo .env _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo .env _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo .env _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo .env kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut .env c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd]; exact hsr.kbuf j hj,
    fun k => memoAt_frame (hsr.memo k) (fun c hc => hfr c (hok.memoDis (.e k) .env c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .env (.e k) kk hkk)) hd,
    fun k => memoAtN_frame (hsr.memoN k) (fun c hc => hfr c (hok.memoDis (.n k) .env c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .env (.n k) kk hkk)) hd,
    fun k => cacheAt_frame (hsr.cache k) (fun c hc => hfr c (hok.memoDis (.c k) .env c (by simp) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .env (.c k) kk hkk)) hd,
    modeAt_frame hsr.mode (fun b k c hc => hfr c (hok.memoDis (.m b k) .env c (by simp) hc))
      (fun b k kk hkk => hfr _ (hok.mdescMemo .env (.m b k) kk hkk)) hd (by rw [hg]),
    ⟨⟨by rw [hg]; exact hH.top, hH.len, hH.lay, fun i hi => by rw [hd]; exact hH.dom i hi,
        fun i hi => by
          have e := hfr _ (hok.envMemo .env i (Nat.lt_of_lt_of_le hi hH.len)); unfold ecell at e
          exact e.trans (hH.val i hi),
        fun i hi => by
          have e := hfr _ (hok.envMemo .env i hi); unfold ecell at e
          exact (hH.words i hi).imp fun w hw => e.trans hw⟩,
      hm, memoAtG_frame hm2 (fun c hc => hfr c (hok.memoDis .tbl .env c (by decide) hc))
        (fun kk hkk => hfr _ (hok.mdescMemo .env .tbl kk hkk)) hd,
      by rw [hg, show (ctxIns C fe EH envM).fe = fe from rfl, hlit]; exact hl⟩, hsr.pins,
    heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo .env i hi)) hd (by rw [hg]), hsr.twf, hden, hsr.floor, hsr.cok⟩

end


/-- The denotation facts `EnvDen` asks of one constant. -/
def NewDen (ci : IConstantInfo) (st : EStore) : Prop :=
  (∀ n ∈ ci.toConstantVal.levelParams, (denoteN st.ns n).isSome = true) ∧
    (denoteE st ci.toConstantVal.type).isSome = true ∧ ci.toConstantVal.levelParams.length + 1 < 2 ^ 60 ∧
    (∀ cv v hint, ci = .defnInfo cv v hint → (denoteE st v).isSome = true) ∧
    (∀ cv caps, ci = .indInfo cv caps → caps.nparams + caps.nIdx < 2 ^ 63)

/-- An environment answering as `fe.push ci` (any literal flags) keeps the denotation facts, given the new
constant's own and that it is not a recursor. -/
theorem envDen_push {fe fe' : IFEnv} {p : Pins} {st : EStore} {ci : IConstantInfo}
    (hf : ∀ n, fe'.find? n = if (ci.name == n) = true then some ci else fe.find? n)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) (hnew : NewDen ci st)
    (hrec : ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) : EnvDen fe' p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  refine ⟨fun c ci' hci => ?_, fun T tbl h' => htb T tbl (by rw [← ht]; exact h'), hp,
    fun c cv mI rP isK rules hci => ?_⟩
  · rw [hf] at hci
    split at hci
    · cases hci; exact hnew
    · exact hc c ci' hci
  · rw [hf] at hci
    split at hci
    · cases hci; exact absurd rfl (hrec cv mI rP isK rules)
    · exact hr c cv mI rP isK rules hci


section
variable {σ : Type}

/-- A call whose callee's post names the context the caller continues in (`Qc … C'` with `SR C'`). -/
theorem specR_callNC {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qc : α → BitVec 64 → AState → Ctx → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ C', Qc a w s' C' ∧ SR C' s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' C', Qc a w s' C' → SpecR (Inv C' s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w C', Qc a w s' C' ∧ Inv C' s' ((x, w) :: Γ) [] D t')
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by
      subst hu
      exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) hcal)
    (fun u hu a w s' st hr => by
      subst hu
      obtain ⟨C', hq, hs⟩ := hRf a w s' st hr
      refine ⟨w, C', hq, ⟨sr_of_eq hs rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w C', Qc a w s' C' ∧ Inv C' s' ((x, w) :: Γ) [] D t')
    hc (fun a s' u ⟨w, C', hq, hu⟩ => hk a w s' C' hq u hu) t rfl

end


def cpS := ofString "cp_s"
def cpD := ofString "cp_d"
def cpI := ofString "cp_i"
def cpN := ofString "cp_n"
def cpW := ofString "cp_w"
def cpR := ofString "cp_r"
def fCpy := ofString "copyToEnv"
def cpParams : List MlS := [cpS, cpD, cpI, cpN]
def cpLocals : List MlS := [cpW, cpR]

/-- Copy words `i … n-1` of a value-heap block at `cpS` into the environment block at `cpD` (after their
length words). -/
def cpyBody : ProgHOL 64 := prologue cpLocals
  (.ite (.cmp .lower (vv cpI) (vv cpN))
    (.seq (.assign .local cpW (.load .one (.op .add [vv cpS, .op .add [.panop .mul [vv cpI, .const 8], .const 8]])))
    (.seq (.store (.op .add [vv cpD, .op .add [.panop .mul [vv cpI, .const 8], .const 8]]) (vv cpW))
    (.seq (.call (some (some (.local, cpR), none)) fCpy [vv cpS, vv cpD, .op .add [vv cpI, .const 1], vv cpN])
      (.return (vv cpR)))))
    (.return (.const 0)))

theorem ecell_idx (C : Ctx) (o i : Nat) :
    ecell C o + (BitVec.ofNat 64 i * 8#64 + 8#64) = ecell C (o + 1 + i) := by
  simp only [ecell, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

section
variable {σ : Type}

theorem cp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cpLocals → (ctxEnv C ++ cpParams.zip vals).get x = none :=
  Knot.params_none C cpLocals cpParams vals (by decide) (by decide)

/-- The copy's answer: the environment image now holds the block's words `i …` at `b + 1 + i …`, cells below
`b + 1 + i` as they were, the length unchanged. -/
def PostCp (C : Ctx) (b : Nat) (xs : List (BitVec 64)) (i : Nat) (EHc : List (BitVec 64)) (_ : Unit) (_ : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ EH', EH'.length = EHc.length ∧ (∀ p, p < b + 1 + i → EH'[p]? = EHc[p]?) ∧
    (∀ j (hj : j < xs.length), i ≤ j → EH'[b + 1 + j]? = some xs[j]) ∧ SR (ctxE C EH') s' st

theorem postCp_locals (C : Ctx) (b : Nat) (xs : List (BitVec 64)) (i : Nat) (EHc : List (BitVec 64)) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCp C b xs i EHc a w s' st → PostCp C b xs i EHc a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH', h1, h2, h3, h4⟩ => ⟨EH', h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

/-- **`cpy`**: the block's words from `i` on, copied. -/
theorem cpy_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (o b : Nat) (xs : List (BitVec 64)) (hb : BlkAt C.H o xs) (hbase : C.EH.length ≤ b)
    (hlen : xs.length < 2 ^ 62) (s : AState) :
    ∀ k i (EHc : List (BitVec 64)), C.EH <+: EHc → b + 1 + xs.length ≤ EHc.length → xs.length - i = k →
      i ≤ xs.length →
      SpecR (σ := σ) (Pre (ctxE C EHc) s (cpParams.zip [cellA C o, ecell C b, BitVec.ofNat 64 i,
        BitVec.ofNat 64 xs.length])) cpyBody s (pure ()) (PostCp C b xs i EHc) := by
  intro k
  induction k with
  | zero =>
    intro i EHc hp hroom hk hi
    have hil : i = xs.length := by omega
    subst hil
    refine specR_prologue (postCp_locals C b xs _ EHc) (cp_none _ _) ?_
    have hlw := nd_lt_iff xs.length xs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EHc, rfl, fun _ _ => rfl, fun j hj hij => absurd hj (by omega),
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i EHc hp hroom hk hi
    have hil : i < xs.length := by omega
    refine specR_prologue (postCp_locals C b xs _ EHc) (cp_none _ _) ?_
    have hlw := nd_lt_iff i xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxE C EHc).H[o + 1 + i]? = some xs[i] := hb.2 i hil
    refine UD.specR_heapLoadI' (C := ctxE C EHc) cpW _ (o + 1 + i) _ hw (by decide)
      (by simp +decide [sev, Env.get, cpParams, ctxEnv]; exact cellA_idx C o i) ?_
    have hok' := ctxOK_E hok hp
    have hj : b + 1 + i < (ctxE C EHc).EH.length := by show _ < EHc.length; omega
    refine specR_envStoreI hok' _ (vv cpW) (b + 1 + i) hj xs[i]
      (by simp +decide [sev, Env.get, cpParams, ctxEnv]; exact ecell_idx C b i) (by simp +decide [Env.get]) ?_
    have hp2 : C.EH <+: EHc.set (b + 1 + i) xs[i] :=
      (prefix_set_ge hp (b + 1 + i) (by have := hp.length_le; omega) xs[i] : _)
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) rfl ?_
    refine specR_callNC (C := ctxE C (EHc.set (b + 1 + i) xs[i])) (D := ctxLocals ++ cpLocals) cpR fCpy cpParams
      [vv cpS, vv cpD, .op .add [vv cpI, .const 1], vv cpN] cpyBody
      [cellA C o, ecell C b, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 xs.length] (by decide) rfl (by decide) hc ?_
      (PostCp C b xs (i + 1) (EHc.set (b + 1 + i) xs[i]))
      (fun _ w s' C' => ∃ EH', C' = ctxE C EH' ∧ EH'.length = EHc.length ∧ (∀ p, p < b + 1 + i → EH'[p]? = EHc[p]?) ∧
        (∀ j (hj : j < xs.length), i ≤ j → EH'[b + 1 + j]? = some xs[j]))
      (fun a w s' st ⟨EH', h1, h2, h3, h4⟩ => ⟨ctxE C EH', ⟨EH', rfl, by rw [h1]; simp, fun p hp' => by
          rw [h2 p (by omega)]; simp [List.getElem?_set]; intro e; omega,
          fun j hj hij => by
            rcases Nat.eq_or_lt_of_le hij with e | e
            · subst e; rw [h2 _ (by omega)]; simp [List.getElem?_set_self, show b + 1 + i < EHc.length by omega]
            · exact h3 j hj e⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cpParams _ rfl hlk)
        (ih (i + 1) _ hp2 (by simp; omega) (by omega) (by omega)))
      (fun _ w s2 C2 ⟨EH2, eC, h1, h2, h3⟩ => ?_)
    · exact ⟨by simp +decide [Env.get, cpParams, ctxEnv], by simp +decide [Env.get, cpParams, ctxEnv],
        by simp +decide [sev, Env.get, cpParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, cpParams, ctxEnv],
        trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH2, h1, h2, h3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
