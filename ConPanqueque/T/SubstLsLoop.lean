import ConPanqueque.T.SubstLsH
import ConPanqueque.T.Ex.AppArgs
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Substituting a level list, element by element

`lsGoS(vs, ks, us, k)`: the handles of the first `k` elements of the list `vs`, each substituted and
re-interned, as a heap block; `k` elements are done by doing `k - 1`, then the last, then appending (the
twin's `internLevelList` order).
-/

namespace ConPanqueque.T
open ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.LSub ConPanqueque.T.ExG ConPanqueque.T.LLeq

theorem internLevelList_append (xs : List ConLeche.Level) (x : ConLeche.Level) :
    internLevelList (xs ++ [x]) =
      (internLevelList xs >>= fun hs => internLevel x >>= fun h => pure (hs ++ [h])) := by
  induction xs with
  | nil => simp [internLevelList]
  | cons y ys ih => simp [internLevelList, ih]

def fLsGoS := ofString "lsGoS"
def pVs := ofString "lvs"
def lsgParams : List MlS := [pVs, pKp, pUs, pGi]

def lsgBody (C : Ctx) : ProgHOL 64 :=
  prologue gaaLocals
  (.ite (.cmp .equal (vv pGi) (.const 0))
    (allocP C lW (.const 8) (.seq (.store (vv lW) (.const 0)) (.return (vv lW))))
    (.seq (.call (some (some (.local, lY), none)) fLsGoS [vv pVs, vv pKp, vv pUs, .op .sub [vv pGi, .const 1]])
    (.seq (.assign .local lDh (vv pVs)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .shift .lsl (.op .sub [vv pGi, .const 1]) (.const 3)])))
    (.seq (.call (some (some (.local, lA1), none)) fSubstM [vv lA1, vv pKp, vv pUs])
    (.seq (.call (some (some (.local, lA2), none)) fInternLv [vv lA1])
    (.seq (.assign .local lCn (.load .one (vv lY)))
    (allocP C lW (.shift .lsl (.op .add [vv lCn, .const 2]) (.const 3))
    (.seq (.store (vv lW) (.op .add [vv lCn, .const 1]))
    (.seq (.assign .local lSrc (.op .add [vv lY, .const 8]))
    (.seq (.assign .local lDst (.op .add [vv lW, .const 8]))
    (.seq (.assign .local lCi (.const 0))
    (.seq copyLoop
    (.seq (.store (vv lDst) (vv lA2))
      (.return (vv lW))))))))))))))))))

section
variable {σ : Type}

/-- The loop's post: the handles as a block of a bigger image; the store grown (levels only). -/
def PostLsG (C : Ctx) (s : AState) (hs : List LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ BlkAt H' o (hs.map Enc.idxW) ∧ SR (ctxH C H') s' st ∧
    StoreWF s'.store ∧ Ext s.store s'.store ∧
    (∃ ls', s' = { s with store := withL s.store ls' } ∧ LGrow s.store.ls ls')

theorem postLsG_locals (C : Ctx) (s : AState) : ∀ (a : List LIdx) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostLsG C s a w s' st → PostLsG C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, a, b, c, d, e⟩ => ⟨H', o, a, b, c, sr_of_eq d rfl rfl rfl rfl, e⟩

theorem params_noneLsg (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ lsgParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ lsgParams := by
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

end

section
variable {σ : Type}

theorem lsg_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
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
    (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (vsH : LsIdx) (uh : List LIdx) (usH : LsIdx)
    (uh2 : List LIdx) (vsL : List ConLeche.Level) (hul : uh.length < 2 ^ 61) :
    ∀ k (H : List (BitVec 64)) (s : AState) (ls : List ConLeche.Level), k ≤ uh.length →
      Frontend.denoteNList s.store.ns khs = some ks → s.store.lss.view vsH = some uh →
      denoteLList s.store.ls uh = some ls → s.store.lss.view usH = some uh2 → denoteLList s.store.ls uh2 = some vsL →
      StoreWF s.store → BlkAt H ko (khs.map Enc.idxW) →
      SpecR (Pre (σ := σ) (ctxH C H) s (lsgParams.zip [Enc.idxW vsH, cellA C ko, Enc.idxW usH, BitVec.ofNat 64 k]))
        (lsgBody C) s (internLevelList ((ls.take k).map (ConLeche.Level.subst ks vsL))) (PostLsG (ctxH C H) s) := by
  intro k
  induction k with
  | zero =>
    intro H s ls _ _ _ _ _ _ hwf _
    refine specR_prologue (postLsG_locals _ _) (params_noneLsg _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, lsgParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_allocI lW (.const 8) 1 (by decide) (by decide) (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
    have hj : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv lW) (.const 0) H2.length hj 0 (by simp [cellA, ctxH]) rfl ?_
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp <;> rfl) (fun t ht => ?_)
    refine ⟨(H2 ++ ws).set H2.length 0, H2.length, ?_, rfl, ?_, sr_of_eq ht.sr rfl rfl rfl rfl, hwf, Ext.refl _,
      ⟨s.store.ls, rfl, LGrow.refl _⟩⟩
    · refine hp.trans (prefix_of_get? (by simp) (fun k hk => ?_))
      rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
    · refine ⟨?_, fun i hi => absurd hi (by simp)⟩
      rw [List.getElem?_set_self (by simp; omega)]; rfl
  | succ k ih =>
    intro H s ls hk hks hv hls hv2 hvs hwf hb
    have hk' : k < uh.length := hk
    obtain ⟨hlu, hgu⟩ := denoteLList_get _ uh ls hls
    have hkl : k < ls.length := by omega
    refine specR_prologue (postLsG_locals _ _) (params_noneLsg _ _) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, lsgParams, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, word_eq_iff (k + 1) 0 (by omega) (by decide)])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some, List.map_append, List.map_singleton,
      internLevelList_append]
    refine specR_callNIH lY fLsGoS lsgParams [vv pVs, vv pKp, vv pUs, .op .sub [vv pGi, .const 1]] (lsgBody C)
      [Enc.idxW vsH, cellA C ko, Enc.idxW usH, BitVec.ofNat 64 k] (by decide) rfl (by decide) hcL
      ⟨by simp +decide [ctxEnv, lsgParams], by simp +decide [ctxEnv, lsgParams] <;> rfl,
        by simp +decide [ctxEnv, lsgParams], by simp +decide [sev, ctxEnv, lsgParams]; exact ofNat_succ_sub_one k,
        trivial⟩
      (fun a w s' st => internLevelList ((ls.take k).map (ConLeche.Level.subst ks vsL)) s = .ok (a, s') ∧
        PostLsG (ctxH C H) s a w s' st)
      (fun a w s' H' => internLevelList ((ls.take k).map (ConLeche.Level.subst ks vsL)) s = .ok (a, s') ∧
        ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW) ∧ StoreWF s'.store ∧ Ext s.store s'.store ∧
          (∃ ls', s' = { s with store := withL s.store ls' } ∧ LGrow s.store.ls ls'))
      (fun a w s' st ⟨hr, H', o, hp, hw, hbk, hsr, hwf', hx, hg⟩ => ⟨H', hp, ⟨hr, o, hw, hbk, hwf', hx, hg⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'; exact ih H s ls (by omega) hks hv hls hv2 hvs hwf hb _ (pre_of_lookups hu lsgParams _ rfl hlk)))
      (fun hs1 w s1 H1 hp1 ⟨hr1, oy, hw, hblk, wf1, ext1, ls1, es1, g1⟩ => ?_)
    subst hw
    subst es1
    have hls1 : denoteLList ls1 uh = some ls := denoteLList_ext ext1.lss.ls uh ls hls
    have hvs1 : denoteLList ls1 uh2 = some vsL := denoteLList_ext ext1.lss.ls uh2 vsL hvs
    have hks1 : Frontend.denoteNList ls1.ns khs = some ks := by rw [g1.2]; exact hks
    obtain ⟨hlu1, hgu1⟩ := denoteLList_get _ uh ls hls1
    refine specR_assignI lDh (vv pVs) (Enc.idxW vsH) (by decide) (by simp +decide [ctxEnv, lsgParams]) ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [ctxEnv, lsgParams] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H1) vsH (by simp +decide) (by simp +decide <;> rfl)
      (by simp +decide [ctxEnv, lsgParams] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
      (fun v1 P1 hv1 _ hl1 => ?_)
    rw [show ({ s with store := withL s.store ls1 } : AState).store.lss.view vsH = s.store.lss.view vsH from rfl, hv]
      at hv1
    cases hv1
    simp only [List.length_map] at hl1
    have m1 := wordsAt_get P1 (uh.map Enc.idxW) k (by simpa using hk') []
    simp only [List.getElem_map] at m1
    refine specR_loadI' lA1 _ (P1 + BitVec.ofNat 64 (8 * k)) _ (Enc.idxW uh[k]) (by decide)
      (by simp +decide [sev, ctxEnv, lsgParams]; rw [show BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k from ofNat_succ_sub_one k, shl_ofNat _ _ (by omega)])
      rfl m1 ?_
    refine specR_congr (m' := pure (ConLeche.Level.subst ks vsL ls[k]) >>= fun t =>
      internLevel t >>= fun h => pure (hs1 ++ [h])) (by simp) ?_
    refine callLv_spec (C := ctxH C H1) lA1 fSubstM substMParams [vv lA1, vv pKp, vv pUs] (substBodyM C)
      [Enc.idxW uh[k], cellA C ko, Enc.idxW usH] (by decide) rfl (by decide) hcS
      ⟨by simp +decide, by simp +decide [ctxEnv, lsgParams] <;> rfl, by simp +decide [ctxEnv, lsgParams], trivial⟩ _
      (substM_spec C hok hcS hcN hcG { s with store := withL s.store ls1 } ko khs ks usH uh2 vsL hks1 hv2 hvs1 ls[k] H1
        (Enc.idxW uh[k]) (blkAt_mono hb hp1) (lrep_arena _ _ _ _ _ _ (hgu1 k hk')))
      (fun H2 c1 hp2 hc1 => ?_)
    refine callIL (C := ctxH C H2) lA2 (vv lA1) internLvBody c1 _ (by decide) hcV (by simp)
      (internLv_spec ra C hok hcZ hcSu hcMx hcIm hcP hcV _ H2 c1 _ wf1 hc1) (fun h s2 hr2 wf2 ⟨ls2, es2, g2⟩ d2 => ?_)
    obtain ⟨-, x2, -, -, -, -, -, -, -⟩ :=
      AM.of_run (P := fun t => t = _) rfl hr2 (internLevel_spec _ _ wf1)
    subst es2
    have hblk2 := blkAt_mono hblk hp2
    obtain ⟨hol, hv0⟩ := blkAt_get0 hblk2
    have hlen := blkAt_len hblk2
    simp only [List.length_map] at hlen hv0
    refine specR_heapLoadI (C := ctxH (ctxH C H) H2) lCn (vv lY) oy hol (by decide) (by simp +decide [cellA, ctxH]) ?_
    rw [show (ctxH (ctxH C H) H2).H[oy]'hol = BitVec.ofNat 64 hs1.length from hv0]
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hlay := hok.heapLay
    have hHN' : H2.length ≤ C.HN := hHN
    refine specR_allocI (C := ctxH (ctxH C H) H2) lW _ (hs1.length + 2) (by omega) (by decide) (fun v => ?_)
      (fun H3 ws hp3 hws hroom => ?_)
    · simp +decide [sev]
      rw [shl_ofNat _ _ (by omega), show (16#64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
      congr 1 <;> omega
    have hp3' : H2 <+: H3 := hp3
    have hH23 := hp3'.length_le
    have hroom' : H3.length + (hs1.length + 2) ≤ C.HN := hroom
    have hq0 : H3.length < (ctxH C (H3 ++ ws)).H.length := by show H3.length < (H3 ++ ws).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok (H3 ++ ws)) (vv lW) (.op .add [vv lCn, .const 1]) H3.length hq0
      (BitVec.ofNat 64 (hs1.length + 1)) (by simp +decide [cellA, ctxH]) (by simp +decide [sev]; exact word_add1_eq _) ?_
    generalize hB : (ctxH C (H3 ++ ws)).H.set H3.length (BitVec.ofNat 64 (hs1.length + 1)) = B
    have hBlen : B.length = H3.length + (hs1.length + 2) := by
      rw [← hB]; show ((H3 ++ ws).set _ _).length = _; simp [hws]
    refine specR_assignI lSrc _ (cellA C (oy + 1)) (by decide) (by simp +decide [sev]; exact cellA_add8 C oy) ?_
    refine specR_assignI lDst _ (cellA C (H3.length + 1)) (by decide)
      (by simp +decide [sev]; exact cellA_add8 C _) ?_
    refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
    have hsrc : ∀ j (hj : j < (hs1.map Enc.idxW).length), B[oy + 1 + j]? = some (hs1.map Enc.idxW)[j] := by
      intro j hj
      rw [← hB]; show ((H3 ++ ws).set _ _)[oy + 1 + j]? = _
      simp only [List.length_map] at hj
      rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
      exact (blkAt_mono hblk2 hp3').2 j (by simpa using hj)
    refine specR_copyI (C := C) hok B (hs1.map Enc.idxW) (oy + 1) (H3.length + 1) (by decide) hsrc
      (by simp; omega) (by simp; omega) (by simp; omega) (by simp +decide) (by decide) (by simp +decide [ctxEnv, lsgParams]) ?_
    generalize hF : fillI B (hs1.map Enc.idxW) (H3.length + 1) (hs1.map Enc.idxW).length = F
    have hFlen : F.length = B.length := by rw [← hF, fillI_length]
    have hdA : H3.length + 1 + (hs1.map Enc.idxW).length < (ctxH C F).H.length := by
      show _ < F.length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok F) (vv lDst) (vv lA2) _ hdA (Enc.idxW h) (by simp +decide [cellA, ctxH])
      (by simp +decide) ?_
    refine specR_returnI (vv lW) (cellA C H3.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hFg : ∀ k, F[k]? = if H3.length + 1 ≤ k ∧ k < H3.length + 1 + hs1.length ∧ k < B.length
        then some ((hs1.map Enc.idxW).getD (k - (H3.length + 1)) 0) else B[k]? := by
      intro k; rw [← hF, fillI_get?]; simp
    refine ⟨F.set (H3.length + 1 + (hs1.map Enc.idxW).length) (Enc.idxW h), H3.length, ?_, rfl, ?_,
      sr_of_eq ht.sr rfl rfl rfl rfl, wf2, ext1.trans x2, ⟨_, rfl, g1.trans g2⟩⟩
    · refine hp1.trans (hp2.trans (hp3'.trans (prefix_of_get? (by simp; omega) (fun k hk => ?_))))
      rw [List.getElem?_set_ne (by simp; omega), hFg k, if_neg (by omega), ← hB]
      show ((H3 ++ ws).set _ _)[k]? = _
      rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
    · refine ⟨?_, fun i hi => ?_⟩
      · rw [List.getElem?_set_ne (by simp <;> omega), hFg, if_neg (by omega), ← hB]
        show ((H3 ++ ws).set _ _)[H3.length]? = _
        rw [List.getElem?_set_self (by simp; omega)]; simp
      · simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at hi
        by_cases e : i = hs1.length
        · subst e
          rw [show H3.length + 1 + hs1.length = H3.length + 1 + (hs1.map Enc.idxW).length by simp,
            List.getElem?_set_self (by simp; omega)]
          simp
        · rw [List.getElem?_set_ne (by simp; omega), hFg, if_pos ⟨by omega, by omega, by omega⟩]
          simp [List.getD_eq_getElem?_getD, show i < hs1.length by omega, List.getElem_append_left]

end

end ConPanqueque.T
