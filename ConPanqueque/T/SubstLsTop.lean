import ConPanqueque.T.SubstLsLoop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `substLsMemoAt` refined

`substLsH(vs, ks, us)`: the loop over all elements, then the list intern of the block; the image is cut
back to the entry image afterwards (the list intern may touch its key words).
-/

namespace ConPanqueque.T
open ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.LSub ConPanqueque.T.ExG ConPanqueque.T.LLeq

section
variable {σ : Type}

/-- A call whose continuation runs at any image the callee's post names (it may shrink). -/
theorem specR_callNIA {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' H', Qx a w s' H' → SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w H', Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by
      subst hu
      exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) hcal)
    (fun u hu a w s' st hr => by
      subst hu
      obtain ⟨H', hq, hs⟩ := hRf a w s' st hr
      refine ⟨w, H', hq, ⟨sr_of_eq hs rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w H', Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    hc (fun a s' u ⟨w, H', hq, hu⟩ => hk a w s' H' hq u hu) t rfl

end

def fSubstLsH := ofString "substLsH"
def slsParams : List MlS := [pVs, pKp, pUs]

def substLsHBody : ProgHOL 64 :=
  prologue gaaLocals
  (.seq (.assign .local lDh (vv pVs)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.seq (.assign .local lCn (vv lRn))
  (.ite (.cmp .lower (vv lCn) (.const (BitVec.ofNat 64 (2 ^ 59))))
    (.seq (.call (some (some (.local, lY), none)) fLsGoS [vv pVs, vv pKp, vv pUs, vv lCn])
    (.seq (.call (some (some (.local, lW), none)) fInternLs [.op .add [vv lY, .const 8], vv lCn])
      (.return (vv lW))))
    hang)))))

section
variable {σ : Type}

theorem params_noneSls (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ slsParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ slsParams := by
    simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hc : (ctxEnv C).get x = none := by
    simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have hz : ∀ (ps : List MlS) (vs : List (BitVec 64)), x ∉ ps → Env.get (ps.zip vs) x = none := by
    intro ps vs hp
    induction ps generalizing vs with
    | nil => rfl
    | cons p ps ih =>
      cases vs with
      | nil => rfl
      | cons v vs =>
        simp only [List.mem_cons, not_or] at hp
        simp only [List.zip_cons_cons, Env.get, hp.1, ite_false]; exact ih vs hp.2
  have happ : ∀ (A B : Env), A.get x = none → B.get x = none → (A ++ B).get x = none := by
    intro A B hA hB
    induction A with
    | nil => exact hB
    | cons p A ih =>
      obtain ⟨y, v⟩ := p
      simp only [List.cons_append, Env.get] at hA ⊢
      split at hA
      · simp at hA
      · rename_i e; simp only [e, ite_false]; exact ih hA
  exact happ _ _ hc (hz _ _ hnot)

/-- `substLsMemoAt`'s post: the list handle; the image kept; the invariants carried on. -/
def PostSLsH (C : Ctx) (s : AState) (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (ls : List ConLeche.Level)
    (h : LsIdx) (w : BitVec 64) (s3 : AState) (st : PState σ) : Prop :=
  w = Enc.idxW h ∧ SR C s3 st ∧ StoreWF s3.store ∧ Ext s.store s3.store ∧ s3.pins = s.pins ∧
    s3.store.pers = s.store.pers ∧ s3.store.scr = s.store.scr ∧ s3.store.scratchOn = s.store.scratchOn ∧
    s3.memos = { s.memos with instLPLsC := s3.memos.instLPLsC } ∧
    s3.caches = { s.caches with readLsC := s3.caches.readLsC } ∧
    ReadLsCacheOK s3.caches.readLsC s3.store ∧ MemoLsOK s3 ks vsL ∧
    denoteLs s3.store.lss h = some (ls.map (ConLeche.Level.subst ks vsL))

theorem substLsH_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubstM = some (substMParams.map (fun p => (p, ShapeHOL.one)), substBodyM C, .one))
    (hcN : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (hcG : C.code.lookup fGoM = some (goParams.map (fun p => (p, ShapeHOL.one)), goBody, .one))
    (hcZ : C.code.lookup fInternLZero = some ([], internLZeroBody, .one))
    (hcSu : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one))
    (hcMx : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one))
    (hcIm : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (hcV : C.code.lookup fInternLv = some ([(pLa, .one)], internLvBody, .one))
    (hcL : C.code.lookup fLsGoS = some (lsgParams.map (fun p => (p, ShapeHOL.one)), lsgBody C, .one))
    (hcIs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (s : AState) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (vsH : LsIdx) (uh : List LIdx) (usH : LsIdx)
    (uh2 : List LIdx) (vsL : List ConLeche.Level) (ls : List ConLeche.Level)
    (hks : Frontend.denoteNList s.store.ns khs = some ks) (hv : s.store.lss.view vsH = some uh)
    (hls : denoteLList s.store.ls uh = some ls) (hv2 : s.store.lss.view usH = some uh2)
    (hvs2 : denoteLList s.store.ls uh2 = some vsL) (hrl : ReadLsCacheOK s.caches.readLsC s.store)
    (hm : MemoLsOK s ks vsL) (hwf : StoreWF s.store) (H : List (BitVec 64)) (hb : BlkAt H ko (khs.map Enc.idxW)) :
    SpecR (Pre (σ := σ) (ctxH C H) s (slsParams.zip [Enc.idxW vsH, cellA C ko, Enc.idxW usH])) substLsHBody s
      (substLsMemoAt ks vsL vsH) (PostSLsH (ctxH C H) s ks vsL ls) := by
  obtain ⟨hlu, hgu⟩ := denoteLList_get _ uh ls hls
  have hdl : denoteLs s.store.lss vsH = some ls := by unfold denoteLs; rw [hv]; exact hls
  refine specR_transfer (m' := internLevels (ls.map (ConLeche.Level.subst ks vsL)) >>= fun h => pure h)
    (R' := fun h w s'' st => w = Enc.idxW h ∧ SR (ctxH C H) s'' st) ?_ ?_
  · refine specR_prologue (fun _ _ _ _ _ ⟨a, b⟩ => ⟨a, sr_of_eq b rfl rfl rfl rfl⟩) (params_noneSls _ _) ?_
    refine specR_assignI lDh (vv pVs) (Enc.idxW vsH) (by decide) (by simp +decide [ctxEnv, slsParams]) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [ctxEnv, slsParams] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) vsH (by simp +decide) (by simp +decide <;> rfl)
      (by simp +decide [ctxEnv, slsParams] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
      (fun v1 P1 hv1 _ hl1 => ?_)
    rw [hv] at hv1; cases hv1
    simp only [List.length_map] at hl1 ⊢
    refine specR_assignI lCn (vv lRn) (BitVec.ofNat 64 uh.length) (by decide) (by simp +decide) ?_
    by_cases hsm : uh.length < 2 ^ 59
    case neg =>
      refine specR_ifI _ 0 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : uh.length < 2 ^ 64)
          (by decide : 2 ^ 59 < 2 ^ 64), hsm]) (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_lt_iff _ _ (by omega : uh.length < 2 ^ 64)
      (by decide : 2 ^ 59 < 2 ^ 64), hsm]) (fun _ => ?_) (fun h => absurd h (by decide))
    have htake : (ls.take uh.length).map (ConLeche.Level.subst ks vsL) = ls.map (ConLeche.Level.subst ks vsL) := by
      rw [List.take_of_length_le (by omega)]
    refine specR_congr (m' := internLevelList ((ls.take uh.length).map (ConLeche.Level.subst ks vsL)) >>= fun hs =>
      internLsNode hs >>= fun h => pure h) (by rw [htake]; simp [internLevels]) ?_
    refine specR_callNIH lY fLsGoS lsgParams [vv pVs, vv pKp, vv pUs, vv lCn] (lsgBody C)
      [Enc.idxW vsH, cellA C ko, Enc.idxW usH, BitVec.ofNat 64 uh.length] (by decide) rfl (by decide) hcL
      ⟨by simp +decide [ctxEnv, slsParams], by simp +decide [ctxEnv, slsParams] <;> rfl,
        by simp +decide [ctxEnv, slsParams], by simp +decide, trivial⟩
      (fun a w s' st => internLevelList ((ls.take uh.length).map (ConLeche.Level.subst ks vsL)) s = .ok (a, s') ∧
        PostLsG (ctxH C H) s a w s' st)
      (fun a w s' H' => internLevelList ((ls.take uh.length).map (ConLeche.Level.subst ks vsL)) s = .ok (a, s') ∧
        ∃ o, H.length ≤ o ∧ w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW) ∧ StoreWF s'.store)
      (fun a w s' st ⟨hr, H', o, hp, ho, hw, hbk, hsr, hwf', _⟩ => ⟨H', hp, ⟨hr, o, ho, hw, hbk, hwf'⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact lsg_spec ra C hok hcS hcN hcG hcZ hcSu hcMx hcIm hcP hcV hcL ko khs ks vsH uh usH uh2 vsL (by omega)
          uh.length H s ls (Nat.le_refl _) hks hv hls hv2 hvs2 hwf hb _ (pre_of_lookups hu lsgParams _ rfl hlk)))
      (fun hs1 w s1 HI hpI ⟨hr1, oy, hoy, hw, hblk, wf1⟩ => ?_)
    subst hw
    obtain ⟨-, -, -, -, -, -, -, -, q9⟩ :=
      AM.of_run (P := fun t => t = s) rfl hr1 (internLevelList_spec s _ hwf)
    obtain ⟨hl9, -⟩ := denoteLList_get _ hs1 _ q9
    simp only [List.length_map, List.length_take] at hl9
    have hlen1 : hs1.length = uh.length := by omega
    have hko := blkAt_len hblk
    simp only [List.length_map] at hko
    refine specR_callNIA lW fInternLs [pKey, lEc] [.op .add [vv lY, .const 8], vv lCn] internLsBody
      [cellA C (oy + 1), BitVec.ofNat 64 hs1.length] (by decide) rfl (by decide) hcIs
      ⟨by simp +decide [sev]; exact cellA_add8 C oy, by simp +decide [hlen1], trivial⟩
      (fun a w s' st => internLsNode hs1 s1 = .ok (a, s') ∧ PostLs (ctxH (ctxH C HI) H) a w s' st)
      (fun a w s' H' => H' = H ∧ internLsNode hs1 s1 = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H, ⟨rfl, hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact internLs_body_spec ra (ctxH C HI) (ctxOK_H hok HI) s1 hs1 (oy + 1) H hpI (by omega) (by
            show oy + 1 + hs1.length ≤ HI.length; omega) (by omega)
          (fun j hj => by have := hblk.2 j (by simpa using hj); simp only [List.getElem_map] at this; exact this)
          _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
      (fun h w s2 H' ⟨e, hr2, hw⟩ => ?_)
    subst e; subst hw
    exact specR_returnI (vv lW) (Enc.idxW h) (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · intro h s'' hrun
    have hrun' : internLevels (ls.map (ConLeche.Level.subst ks vsL)) s = .ok (h, s'') := by
      have e : (internLevels (ls.map (ConLeche.Level.subst ks vsL)) >>= fun h => pure h : AM LsIdx) s =
          internLevels (ls.map (ConLeche.Level.subst ks vsL)) s := by simp only [bind_pure]
      rw [← e]; exact hrun
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      AM.of_run (P := fun t => t = s) rfl hrun' (internLevels_spec s _ hwf)
    obtain ⟨s3, h3, e3, p3, m3, c3, r3, ml3⟩ := substLsMemoAt_run ks vsL s vsH ls hdl hrl hm hwf h s'' hrun'
    refine ⟨s3, h3, fun w st ⟨hw, hsr⟩ => ⟨hw, sr_lpl hsr e3 ?_ ?_ ?_, by rw [e3]; exact q1, by rw [e3]; exact q2, p3,
      by rw [e3]; exact q3, by rw [e3]; exact q4, by rw [e3]; exact q5, m3, c3, r3, ml3, by rw [e3]; exact q9⟩⟩
    · rw [m3, q6]
    · rw [c3, q7]; exact mirrorEq_refl _
    · rw [p3, q8]

end

end ConPanqueque.T
