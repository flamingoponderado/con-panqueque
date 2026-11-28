import ConPanqueque.T.Ind.ClassNfs
import ConPanqueque.T.Ind.NestPos

/-!
# A class's constructor for the generator: its first table entry, its minor slot, its record

`ffe`: the first table entry of a constructor (none hangs).  `cms`: the count of a constructor's minor slots.
`CCRep`: a class constructor's record (its fields' kinds a block).  `classCtorOf` itself is in `ClassCtorRec`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The first entry of a constructor -/

def ffeT := ofString "ffe_t"
def ffeI := ofString "ffe_i"
def ffeK := ofString "ffe_k"
def ffeC := ofString "ffe_c"
def ffeP := ofString "ffe_p"
def ffeX := ofString "ffe_x"
def ffeR := ofString "ffe_r"
def fFfe := ofString "firstEntry"

def ffeParams : List MlS := [ffeT, ffeI, ffeK, ffeC]
def ffeLocals : List MlS := [ffeP, ffeX, ffeR]

def ffeBody : ProgHOL 64 := prologue ffeLocals
  (.ite (.cmp .lower (vv ffeI) (vv ffeK))
    (.seq (.assign .local ffeP (.load .one (.op .add [vv ffeT, .op .add [.panop .mul [vv ffeI, .const 8], .const 8]])))
    (.seq (.assign .local ffeX (.load .one (vv ffeP)))
    (.ite (.cmp .equal (vv ffeX) (vv ffeC)) (.return (vv ffeP))
      (.seq (.call (some (some (.local, ffeR), none)) fFfe [vv ffeT, .op .add [vv ffeI, .const 1], vv ffeK, vv ffeC])
        (.return (vv ffeR))))))
    hang)

section
variable {σ : Type}

theorem ffe_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ffeLocals → (ctxEnv C ++ ffeParams.zip vals).get x = none :=
  Knot.params_none C ffeLocals ffeParams vals (by decide) (by decide)

/-- An entry list's first element at a constructor, as a record (the state kept). -/
def PostFE (C : Ctx) (s : AState) (r : List NestCtorNf) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ e es o, r = e :: es ∧ w = cellA C o ∧ NfRep C C.H o e ∧ SR C s' st

/-- **The first entry of `cn`** from entry `i` on (none hangs). -/
theorem ffe_spec (C : Ctx) (hc : C.code.lookup fFfe = some (ffeParams.map (fun p => (p, ShapeHOL.one)), ffeBody, .one))
    (tbl : List NestCtorNf) (ot : Nat) (htl : tbl.length < 2 ^ 58) (cn : NIdx) (H : List (BitVec 64))
    (htb : PRep C H ot (fun H o nf => NfRep C H o nf) tbl) :
    ∀ f i (s : AState), tbl.length - i = f → i ≤ tbl.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (ffeParams.zip [cellA C ot, BitVec.ofNat 64 i, BitVec.ofNat 64 tbl.length,
        Enc.idxW cn])) ffeBody s (pure ((tbl.drop i).filter (·.ctor == cn))) (PostFE (ctxH C H) s) := by
  obtain ⟨os, hosl, hosb, hosr⟩ := htb
  have hpost : ∀ (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostFE (ctxH C H) s a w s' st → PostFE (ctxH C H) s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ ⟨h0, e, es, o, h1, h2, h3, h4⟩ => ⟨h0, e, es, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = tbl.length := by omega
    subst hin
    refine specR_prologue (hpost s) (ffe_none _ _) ?_
    have hlw := nd_lt_iff tbl.length tbl.length (by omega) (by omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ffeParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  | succ f ih =>
    intro i s hf hi
    have hin : i < tbl.length := by omega
    refine specR_prologue (hpost s) (ffe_none _ _) ?_
    have hlw := nd_lt_iff i tbl.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ffeParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hio : i < os.length := by omega
    have hpe := hosb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hnf := hosr i hin hio
    refine UD.specR_heapLoadI' (C := ctxH C H) ffeP _ (ot + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get, ffeParams, ctxEnv]; exact cellA_mulIdx C ot i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffeX (vv ffeP) _ _ hnf.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.filter_cons]
    by_cases he : tbl[i].ctor = cn
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [he, beq_self_eq_true, ↓reduceIte]
      exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, tbl[i], _, os[i], rfl, rfl, hnf,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hne : Enc.idxW tbl[i].ctor ≠ Enc.idxW cn := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    have hbe : (tbl[i].ctor == cn) = false := beq_eq_false_iff_ne.mpr he
    simp only [hbe, Bool.false_eq_true, ↓reduceIte]
    refine specR_congr (m' := (pure ((tbl.drop (i + 1)).filter (·.ctor == cn)) : AM (List NestCtorNf)) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ffeR fFfe ffeParams [vv ffeT, .op .add [vv ffeI, .const 1], vv ffeK, vv ffeC]
      ffeBody [cellA C ot, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 tbl.length, Enc.idxW cn] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ffeParams, ctxEnv], trivial⟩
      (PostFE (ctxH C H) s) (fun r w s' H' => H' = H ∧ s' = s ∧ ∃ e es o, r = e :: es ∧ w = cellA C o ∧ NfRep C H o e)
      (fun r w s' st ⟨h0, e, es, o, h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, e, es, o, h1, h2, h3⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ffeParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun r w s3 H3 hp3 ⟨eH, es3, e, es, o, h1, h2, h3⟩ => ?_)
    subst eH es3 h2
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨rfl, e, es, o, h1, rfl, h3,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `classMinorSlot` at a class `c` -/

/-- A minor slot of class `c` at constructor `cn`. -/
def isHitC (c : Nat) (cn : NIdx) : ClassSlot → Bool
  | .minor c' C _ => c' == c && C == cn
  | .motive _ => false

def ihsOf : ClassSlot → List (Nat × Nat)
  | .minor _ _ ihs => ihs
  | .motive _ => []

/-- The twin's hit function of `classMinorSlot rd c cn`. -/
def cmsHit (l : List ClassSlot) (c : Nat) (cn : NIdx) (s : Nat) : Option (Nat × List (Nat × Nat)) :=
  match (l[s]? : Option ClassSlot) with
  | some (.minor c' C' ihs) => if c' == c && C' == cn then some (s, ihs) else none
  | _ => none

theorem cmsHits_cons (a : ClassSlot) (l : List ClassSlot) (c : Nat) (cn : NIdx) :
    (List.range (a :: l).length).filterMap (cmsHit (a :: l) c cn) =
      (cmsHit [a] c cn 0).toList ++ ((List.range l.length).filterMap (cmsHit l c cn)).map (fun h => (h.1 + 1, h.2)) := by
  rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, List.map_filterMap]
  have h0 : cmsHit (a :: l) c cn 0 = cmsHit [a] c cn 0 := by simp [cmsHit]
  have h1 : ∀ s, cmsHit (a :: l) c cn (s + 1) = (cmsHit l c cn s).map (fun h => (h.1 + 1, h.2)) := by
    intro s; unfold cmsHit; simp only [List.getElem?_cons_succ]
    split <;> simp_all
  rw [h0]
  have h2 : (List.range l.length).filterMap (cmsHit (a :: l) c cn ∘ Nat.succ) =
      (List.range l.length).filterMap (fun s => (cmsHit l c cn s).map (fun h => (h.1 + 1, h.2))) := by
    congr 1; funext s; exact h1 s
  rw [h2]
  cases cmsHit [a] c cn 0 <;> rfl

theorem cmsHits_props (c : Nat) (cn : NIdx) : ∀ l : List ClassSlot,
    ((List.range l.length).filterMap (cmsHit l c cn)).length = (l.filter (isHitC c cn)).length ∧
    ∀ h ∈ (List.range l.length).filterMap (cmsHit l c cn), ∃ sl ∈ l, isHitC c cn sl = true ∧ h.2 = ihsOf sl
  | [] => by simp
  | a :: l => by
    obtain ⟨ih1, ih2⟩ := cmsHits_props c cn l
    rw [cmsHits_cons]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, List.length_map, ih1, List.filter_cons]
      cases a with
      | motive k => simp [cmsHit, isHitC]
      | minor c0 C ihs =>
        by_cases hh : (c0 == c && C == cn) = true
        · simp [cmsHit, isHitC, hh]; omega
        · simp only [Bool.not_eq_true] at hh; simp [cmsHit, isHitC, hh]
    · intro h hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases a with
        | motive k => simp [cmsHit] at hm
        | minor c0 C ihs =>
          by_cases hh : (c0 == c && C == cn) = true
          · simp [cmsHit, hh] at hm; subst hm; exact ⟨_, List.mem_cons_self, by simp [isHitC, hh], rfl⟩
          · simp only [Bool.not_eq_true] at hh; simp [cmsHit, hh] at hm
      · rw [List.mem_map] at hm
        obtain ⟨h', hm', rfl⟩ := hm
        obtain ⟨sl, hsl, hh, he⟩ := ih2 h' hm'
        exact ⟨sl, List.mem_cons_of_mem _ hsl, hh, he⟩

/-- The inductive hypotheses of the first minor slot at `(c, cn)`. -/
def firstIhs (c : Nat) (cn : NIdx) (l : List ClassSlot) : List (Nat × Nat) := ((l.find? (isHitC c cn)).map ihsOf).getD []

/-- One minor slot at `(c, cn)`: `classMinorSlot` answers it, with its inductive hypotheses. -/
theorem classMinorSlot_one (rd : ClassRead) (c : Nat) (cn : NIdx) (h1 : (rd.slots.filter (isHitC c cn)).length = 1) :
    ∃ k, classMinorSlot rd c cn = pure (k, firstIhs c cn rd.slots) := by
  obtain ⟨hl, hp⟩ := cmsHits_props c cn rd.slots
  rw [h1] at hl
  obtain ⟨h, hh⟩ := List.length_eq_one_iff.mp hl
  obtain ⟨sl, hsl, hhit, he⟩ := hp h (by rw [hh]; exact List.mem_singleton_self _)
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
  have hsx : sl = x := by
    have : sl ∈ rd.slots.filter (isHitC c cn) := List.mem_filter.mpr ⟨hsl, hhit⟩
    rw [hx] at this; simpa using this
  have hfind : firstIhs c cn rd.slots = ihsOf x := by
    unfold firstIhs
    obtain ⟨y, hy⟩ : ∃ y, rd.slots.find? (isHitC c cn) = some y := by
      rcases h : rd.slots.find? (isHitC c cn) with _ | y
      · exact absurd (List.find?_eq_none.mp h sl hsl) (by simp [hhit])
      · exact ⟨y, rfl⟩
    have hym := List.mem_of_find?_eq_some hy
    have hyp := List.find?_some hy
    have : y ∈ rd.slots.filter (isHitC c cn) := List.mem_filter.mpr ⟨hym, hyp⟩
    rw [hx] at this
    simp only [List.mem_singleton] at this
    rw [hy, this]; rfl
  have hih : h.2 = firstIhs c cn rd.slots := by rw [hfind, he, hsx]
  have key : (List.range rd.slots.length).filterMap (cmsHit rd.slots c cn) = [(h.1, firstIhs c cn rd.slots)] := by
    rw [hh, ← hih]
  have e : ∀ f : Nat → Option (Nat × List (Nat × Nat)), (∀ k, f k = cmsHit rd.slots c cn k) →
      (List.range rd.slots.length).filterMap f = [(h.1, firstIhs c cn rd.slots)] := by
    intro f hf; rw [← key]; congr 1; funext k; exact hf k
  refine ⟨h.1, ?_⟩
  unfold classMinorSlot
  rw [e _ (fun k => by unfold cmsHit; rcases rd.slots[k]? with _ | (_ | _) <;> rfl)]

def cmsS := ofString "cms_s"
def cmsI := ofString "cms_i"
def cmsN := ofString "cms_n"
def cmsCn := ofString "cms_cn"
def cmsK := ofString "cms_k"
def cmsP := ofString "cms_p"
def cmsTg := ofString "cms_tg"
def cmsR := ofString "cms_r"
def cmsCc := ofString "cms_cc"
def cmsCv := ofString "cms_cv"
def cmsIh := ofString "cms_ih"
def cmsL := ofString "cms_l"
def fCms := ofString "minorSlotCount"

def cmsParams : List MlS := [cmsS, cmsI, cmsN, cmsCn, cmsK]
def cmsLocals : List MlS := [cmsP, cmsTg, cmsR, cmsCc, cmsCv]

def cmsBody : ProgHOL 64 := prologue cmsLocals
  (.ite (.cmp .lower (vv cmsI) (vv cmsN))
    (.seq (.assign .local cmsP (.load .one (.op .add [vv cmsS, .op .add [.panop .mul [vv cmsI, .const 8], .const 8]])))
    (.seq (.assign .local cmsTg (.load .one (vv cmsP)))
    (.seq (.call (some (some (.local, cmsR), none)) fCms [vv cmsS, .op .add [vv cmsI, .const 1], vv cmsN, vv cmsCn, vv cmsK])
    (.ite (.cmp .equal (vv cmsTg) (.const 1))
      (.seq (.assign .local cmsCc (.load .one (.op .add [vv cmsP, .const 8])))
      (.seq (.assign .local cmsCv (.load .one (.op .add [vv cmsP, .const 16])))
      (.ite (.cmp .equal (vv cmsCc) (vv cmsK))
        (.ite (.cmp .equal (vv cmsCv) (vv cmsCn))
          (.return (.op .add [vv cmsR, .const 1]))
          (.return (vv cmsR)))
        (.return (vv cmsR)))))
      (.return (vv cmsR))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem cms_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmsLocals → (ctxEnv C ++ cmsParams.zip vals).get x = none :=
  Knot.params_none C cmsLocals cmsParams vals (by decide) (by decide)

/-- The count of minor slots at `(cc, cn)`, each without inductive hypotheses (else a hang). -/
def PostCMS (C : Ctx) (sls : List ClassSlot) (cn : NIdx) (s : AState) (r : Nat) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ sls.length ∧ SR C s' st

set_option maxHeartbeats 16000000 in
theorem cms_spec (C : Ctx) (hc : C.code.lookup fCms = some (cmsParams.map (fun p => (p, ShapeHOL.one)), cmsBody, .one))
    (sls : List ClassSlot) (os : Nat) (hsl : sls.length < 2 ^ 58) (cn : NIdx) (cc : Nat) (hcc : cc < 2 ^ 63)
    (hcb : ∀ sl ∈ sls, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63) (H : List (BitVec 64))
    (hsb : SlotBlk C H os sls) :
    ∀ f i (s : AState), sls.length - i = f → i ≤ sls.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cmsParams.zip [cellA C os, BitVec.ofNat 64 i, BitVec.ofNat 64 sls.length,
        Enc.idxW cn, BitVec.ofNat 64 cc])) cmsBody s (pure ((sls.drop i).filter (isHitC cc cn)).length)
        (PostCMS (ctxH C H) (sls.drop i) cn s) := by
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := hsb
  have hpost : ∀ (l : List ClassSlot) (s : AState) a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
      PostCMS (ctxH C H) l cn s a w s' st → PostCMS (ctxH C H) l cn s a w s' { st with locals := L } :=
    fun _ _ _ _ _ _ _ ⟨h0, h1, h2, h4⟩ => ⟨h0, h1, h2, sr_of_eq h4 rfl rfl rfl rfl⟩
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = sls.length := by omega
    subst hin
    refine specR_prologue (hpost _ s) (cms_none _ _) ?_
    have hlw := nd_lt_iff sls.length sls.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, rfl, by simp, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < sls.length := by omega
    refine specR_prologue (hpost _ s) (cms_none _ _) ?_
    have hlw := nd_lt_iff i sls.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨op, hop, hsr⟩ := hpsr i hin
    have hio : i < ps.length := by omega
    have hpe := hpsb.2 i (by simp; omega)
    simp only [List.getElem_map] at hpe
    have hpi : ps[i] = op := by simpa [List.getElem?_eq_getElem hio] using hop
    rw [hpi] at hpe
    refine UD.specR_heapLoadI' (C := ctxH C H) cmsP _ (os + 1 + i) _ hpe (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv]; exact cellA_mulIdx C os i (by omega)) ?_
    have hsli := List.getElem_mem hin
    rw [List.drop_eq_getElem_cons hin]
    generalize hsl : sls[i] = sl at hsr hsli
    have hcb' := hcb sl hsli
    cases sl with
    | motive k =>
      obtain ⟨h0, -, -, -⟩ := hsr
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsTg (vv cmsP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_congr (m' := (pure ((sls.drop (i + 1)).filter (isHitC cc cn)).length : AM Nat) >>= fun r => pure r)
        (by simp [List.filter_cons, isHitC]) ?_
      refine specR_callNIH (C := ctxH C H) cmsR fCms cmsParams [vv cmsS, .op .add [vv cmsI, .const 1], vv cmsN, vv cmsCn, vv cmsK]
        cmsBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, Enc.idxW cn, BitVec.ofNat 64 cc] (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], trivial⟩
        (PostCMS (ctxH C H) (sls.drop (i + 1)) cn s)
        (fun r w s' H' => H' = H ∧ s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ (sls.drop (i + 1)).length)
        (fun r w s' st ⟨h0, h1, h2, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, h1, h2⟩, h4⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmsParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun r w s3 H3 hp3 ⟨eH, es, hw, hr⟩ => ?_)
      subst H3 s3 hw
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, rfl, by simp at hr ⊢; omega,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | minor c C' ihs =>
      obtain ⟨h0, h1, h2, -⟩ := hsr
      have hc63 := hcb' c C' ihs rfl
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsTg (vv cmsP) op _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
      refine specR_congr (m' := (pure ((sls.drop (i + 1)).filter (isHitC cc cn)).length : AM Nat) >>= fun r =>
        pure (if isHitC cc cn (.minor c C' ihs) then r + 1 else r)) (by simp [List.filter_cons]; split <;> simp) ?_
      refine specR_callNIH (C := ctxH C H) cmsR fCms cmsParams [vv cmsS, .op .add [vv cmsI, .const 1], vv cmsN, vv cmsCn, vv cmsK]
        cmsBody [cellA C os, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 sls.length, Enc.idxW cn, BitVec.ofNat 64 cc] (by decide) rfl (by decide) hc
        ⟨by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv]; exact word_add1_eq i, by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv], trivial⟩
        (PostCMS (ctxH C H) (sls.drop (i + 1)) cn s)
        (fun r w s' H' => H' = H ∧ s' = s ∧ w = BitVec.ofNat 64 r ∧ r ≤ (sls.drop (i + 1)).length)
        (fun r w s' st ⟨h0, h1, h2, h4⟩ => ⟨H, List.prefix_refl _, ⟨rfl, h0, h1, h2⟩, h4⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmsParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
        (fun r w s3 H3 hp3 ⟨eH, es, hw, hr⟩ => ?_)
      subst H3 s3 hw
      obtain ⟨hc63', hil⟩ := hc63
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsCc _ (op + 1) _ h1 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) cmsCv _ (op + 2) _ h2 (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
      have hret : isHitC cc cn (.minor c C' ihs) = false → ∀ (Γ : Env), Γ.get cmsR = some (BitVec.ofNat 64 r) →
          SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ cmsLocals)) (.return (vv cmsR)) s
            (pure (if isHitC cc cn (.minor c C' ihs) then r + 1 else r))
            (PostCMS (ctxH C H) (.minor c C' ihs :: sls.drop (i + 1)) cn s) := by
        intro hf Γ gR
        refine specR_returnI _ (BitVec.ofNat 64 r) (by simp [sev, gR]) (fun t ht => ?_)
        rw [hf]
        exact ⟨rfl, by simp, by simp at hr ⊢; omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩
      by_cases hc0 : c = cc
      swap
      · have hne : BitVec.ofNat 64 c ≠ BitVec.ofNat 64 cc := fun e => hc0 (by have := congrArg BitVec.toNat e; simp at this; omega)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
        refine hret (by simp [isHitC, hc0]) _ ?_
        simp +decide [Env.get_cons]
      subst hc0
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      by_cases hcv : C' = cn
      swap
      · have hne : Enc.idxW C' ≠ Enc.idxW cn := fun e => hcv (Enc.idxW_inj e)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        refine hret (by simp [isHitC, hcv]) _ ?_
        simp +decide [Env.get_cons]
      subst C'
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cmsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      have hh : ∀ c0, isHitC c0 cn (.minor c0 cn ihs) = true := fun c0 => by simp [isHitC]
      refine specR_returnI _ (BitVec.ofNat 64 (r + 1)) (by simp +decide [sev, Env.get_cons]; exact word_add1_eq r)
        (fun t ht => ?_)
      rw [hh]
      exact ⟨rfl, by simp, by simp at hr ⊢; omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

/-! ## A class constructor's record -/

/-- A class field's word: `0` ordinary, `(tele + 1) + 2 ^ 32 * c` recursive at class `c`. -/
def cfKindW : ClassField → BitVec 64
  | .ordinary => 0
  | .recursive c tele => BitVec.ofNat 64 (tele + 1 + 2 ^ 32 * c)

/-- Every recursive field's telescope (plus one) below `2 ^ 32`, its class below `2 ^ 24`. -/
def KindsOK (ks : List ClassField) : Prop :=
  ∀ k ∈ ks, k = .ordinary ∨ ∃ c tele, k = .recursive c tele ∧ tele + 1 < 2 ^ 32 ∧ c < 2 ^ 24

/-- A class constructor `[cv, nF, tyD, tyN, |kinds|, kinds]`, the kinds a block of `cfKindW`s. -/
def CCRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (cc : ClassCtor) : Prop :=
  (∃ ocv, H[o]? = some (cellA C ocv) ∧ CVRep C H ocv cc.cv) ∧ H[o + 1]? = some (BitVec.ofNat 64 cc.nF) ∧
    H[o + 2]? = some (Enc.idxW cc.tyD) ∧ H[o + 3]? = some (Enc.idxW cc.tyN) ∧
    H[o + 4]? = some (BitVec.ofNat 64 cc.kinds.length) ∧
    (∃ ok, H[o + 5]? = some (cellA C ok) ∧ BlkAt H ok (cc.kinds.map cfKindW)) ∧ KindsOK cc.kinds ∧
    cc.kinds.length = cc.nF

section
variable {σ : Type}

/-- Class constructors, as a block of records. -/
def PostCCs (C : Ctx) (ccs : List ClassCtor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ PRep C H' o (fun H o cc => CCRep C H o cc) ccs ∧ SR (ctxH C H') s' st

theorem postCCs_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCCs C a w s' st → PostCCs C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem ccRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {cc : ClassCtor}
    (h : CCRep C H o cc) : CCRep C H' o cc :=
  let ⟨⟨ocv, a1, a2⟩, b, c, d, e, ⟨ok, f1, f2⟩, g, g'⟩ := h
  ⟨⟨ocv, get_prefix a1 hp, cvRep_mono hp a2⟩, get_prefix b hp, get_prefix c hp, get_prefix d hp, get_prefix e hp,
    ⟨ok, get_prefix f1 hp, blkAt_mono f2 hp⟩, g, g'⟩

end

end ConPanqueque.T.Ind
