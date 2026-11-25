import ConPanqueque.T.Copy
import ConPanqueque.T.Ex.Small
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `getAppArgs`

The arguments of an application spine, as a block. `gaa(fu, h)`: on an `app f a`, the block of `f`'s
arguments is copied into a fresh block one longer, `a` appended; otherwise a fresh empty block.
-/

namespace ConPanqueque.T.ExG
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM

def fGaa := ofString "getAppArgs"

def gaaLocals : List MlS := inst1Locals ++ [lSrc, lDst, lCi, lCz, lCn]

def leafG (C : Ctx) : ProgHOL 64 :=
  allocP C lW (.const 8) (.seq (.store (vv lW) (.const 0)) (.return (vv lW)))

def appG (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.call (some (some (.local, lY), none)) fGaa [.op .sub [vv pFu, .const 1], vv lA1])
    (.seq (.assign .local lCn (.load .one (vv lY)))
    (allocP C lW (.shift .lsl (.op .add [vv lCn, .const 2]) (.const 3))
    (.seq (.store (vv lW) (.op .add [vv lCn, .const 1]))
    (.seq (.assign .local lSrc (.op .add [vv lY, .const 8]))
    (.seq (.assign .local lDst (.op .add [vv lW, .const 8]))
    (.seq (.assign .local lCi (.const 0))
    (.seq copyLoop
    (.seq (.store (vv lDst) (vv lA2))
      (.return (vv lW)))))))))))))))

def gaaCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang (.ite (isAppE (vv pH)) (appG C) (leafG C))

def gaaBody (C : Ctx) : ProgHOL 64 := prologue gaaLocals (gaaCore C)

abbrev DG : List MlS := ctxLocals ++ gaaLocals

section
variable {σ : Type}

theorem leafG_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} :
    SpecR (Inv (σ := σ) C s Γ M DG) (leafG C) s (pure []) (PostA C) := by
  unfold leafG
  refine specR_allocI lW (.const 8) 1 (by decide) (by decide) (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  have hj : H2.length < (ctxH C (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv lW) (.const 0) H2.length hj 0 (by simp [cellA, ctxH]) rfl ?_
  refine specR_returnI (vv lW) (cellA C H2.length) (by simp) (fun t ht => ?_)
  refine ⟨(H2 ++ ws).set H2.length 0, H2.length, ?_, rfl, ?_, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · refine hp.trans (prefix_of_get? (by simp) (fun k hk => ?_))
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
  · refine ⟨?_, fun i hi => absurd hi (by simp)⟩
    rw [List.getElem?_set_self (by simp; omega)]; rfl

end

section
variable {σ : Type}

def RecG (C : Ctx) (n : Nat) : Prop :=
  ∀ (H : List (BitVec 64)) (h : EIdx) (s : AState),
    SpecR (Pre (σ := σ) (ctxH C H) s [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]) (gaaBody C) s
      (getAppArgs n h) (PostA (ctxH C H))

theorem appG_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one))
    (n : Nat) (ih : RecG (σ := σ) C n) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    (h : EIdx) (h4 : h.tag = 4) (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1)))
    (hh : Γ.get pH = some (Enc.idxW h)) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hz : Γ.get lCz = none) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DG) (appG C) s
      (do match ← viewApp h with
        | none => failDanglingE
        | some (f, a) => do let as ← getAppArgs n f; pure (as ++ [a])) (PostA (ctxH C H)) := by
  unfold appG
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_viewAppI h h4 (by simp) (by simp +decide <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun f a P => ?_)
  refine specR_loadI' lA1 _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + 8) (P + 8) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine specR_call2IH lY fGaa pFu pH (by decide) _ _ (gaaBody C) (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW f)
    (by decide) hcode (by simp +decide [sev, hfu]) (by simp +decide) (PostA (ctxH C H))
    (fun as w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (as.map Enc.idxW))
    (fun _ _ _ _ ⟨H', o, hp, hw, hb, hs⟩ => ⟨H', hp, ⟨o, hw, hb⟩, hs⟩)
    (fun u hu _ h1 h2 w hw => by
      subst hw; rw [ofNat_succ_sub_one] at h1; exact ih H f s _ (pre2 hu _ _ _ _ h1 h2))
    (fun as w s1 H1 hp1 ⟨oy, hw, hblk⟩ => ?_)
  subst hw
  obtain ⟨hol, hv0⟩ := blkAt_get0 hblk
  have hlen := blkAt_len hblk
  simp only [List.length_map] at hlen hv0
  refine specR_heapLoadI (C := ctxH (ctxH C H) H1) lCn (vv lY) oy hol (by decide) (by simp +decide [cellA, ctxH]) ?_
  rw [show (ctxH (ctxH C H) H1).H[oy]'hol = BitVec.ofNat 64 as.length from hv0]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have hHN' : H1.length ≤ C.HN := hHN
  refine specR_allocI (C := ctxH (ctxH C H) H1) lW _ (as.length + 2) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev]
    rw [shl_ofNat _ _ (by omega), show (16#64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    congr 1 <;> omega
  have hp2' : H1 <+: H2 := hp2
  have hH12 := hp2'.length_le
  have hroom' : H2.length + (as.length + 2) ≤ C.HN := hroom
  have hq0 : H2.length < (ctxH C (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok (H2 ++ ws)) (vv lW) (.op .add [vv lCn, .const 1]) H2.length hq0
    (BitVec.ofNat 64 (as.length + 1)) (by simp +decide [cellA, ctxH]) (by simp +decide [sev]; exact word_add1_eq _) ?_
  generalize hB : (ctxH C (H2 ++ ws)).H.set H2.length (BitVec.ofNat 64 (as.length + 1)) = B
  have hBlen : B.length = H2.length + (as.length + 2) := by rw [← hB]; show ((H2 ++ ws).set _ _).length = _; simp [hws]
  refine specR_assignI lSrc _ (cellA C (oy + 1)) (by decide) (by simp +decide [sev]; exact cellA_add8 C oy) ?_
  refine specR_assignI lDst _ (cellA C (H2.length + 1)) (by decide)
    (by simp +decide [sev]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  have hsrc : ∀ j (hj : j < (as.map Enc.idxW).length), B[oy + 1 + j]? = some (as.map Enc.idxW)[j] := by
    intro j hj
    rw [← hB]; show ((H2 ++ ws).set _ _)[oy + 1 + j]? = _
    simp only [List.length_map] at hj
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
    exact (blkAt_mono hblk hp2').2 j (by simpa using hj)
  refine specR_copyI (C := C) hok B (as.map Enc.idxW) (oy + 1) (H2.length + 1) (by decide) hsrc
    (by simp; omega) (by simp; omega) (by simp; omega) (by simp +decide) (by decide) (by simp +decide [hz]) ?_
  generalize hF : fillI B (as.map Enc.idxW) (H2.length + 1) (as.map Enc.idxW).length = F
  have hFlen : F.length = B.length := by rw [← hF, fillI_length]
  have hdA : H2.length + 1 + (as.map Enc.idxW).length < (ctxH C F).H.length := by
    show _ < F.length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok F) (vv lDst) (vv lA2) _ hdA (Enc.idxW a) (by simp +decide [cellA, ctxH])
    (by simp +decide) ?_
  refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
  have hFg : ∀ k, F[k]? = if H2.length + 1 ≤ k ∧ k < H2.length + 1 + as.length ∧ k < B.length
      then some ((as.map Enc.idxW).getD (k - (H2.length + 1)) 0) else B[k]? := by
    intro k; rw [← hF, fillI_get?]; simp
  refine ⟨F.set (H2.length + 1 + (as.map Enc.idxW).length) (Enc.idxW a), H2.length, ?_, rfl, ?_,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · refine hp1.trans (hp2'.trans (prefix_of_get? (by simp; omega) (fun k hk => ?_)))
    rw [List.getElem?_set_ne (by simp; omega), hFg k, ite_eq_right (by omega), ← hB]
    show ((H2 ++ ws).set _ _)[k]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
  · refine ⟨?_, fun i hi => ?_⟩
    · rw [List.getElem?_set_ne (by simp <;> omega), hFg, ite_eq_right (by omega), ← hB]
      show ((H2 ++ ws).set _ _)[H2.length]? = _
      rw [List.getElem?_set_self (by simp; omega)]; simp
    · simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at hi
      by_cases e : i = as.length
      · subst e
        rw [show H2.length + 1 + as.length = H2.length + 1 + (as.map Enc.idxW).length by simp,
          List.getElem?_set_self (by simp; omega)]
        simp
      · rw [List.getElem?_set_ne (by simp; omega), hFg, ite_eq_left ⟨by omega, by omega, by omega⟩]
        simp [List.getD_eq_getElem?_getD, show i < as.length by omega, List.getElem_append_left]

theorem params_noneG (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ [(pFu, va), (pH, vb)]).get x = none := by
  intro x hx
  simp only [gaaLocals, inst1Locals, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem gaa_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)) :
    ∀ n, n < 2 ^ 64 → RecG (σ := σ) C n := by
  intro n
  induction n with
  | zero =>
    intro _ H h s
    refine specR_prologue (postA_locals _) (params_noneG _ _ _) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf H h s
    have ih' := ih (by omega)
    refine specR_prologue (postA_locals _) (params_noneG _ _ _) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    simp only [getAppArgs]
    refine specR_iteI (isAppE (vv pH)) (isAppW (Enc.idxW h)) ?_
      (by rw [isApp_iff]; simp [ETag.app]) (fun hb => ?_) (fun _ => ?_)
    · exact Ex2.sev_isApp _ pH _ (by simp +decide [ctxEnv])
    · have h4 : h.tag = 4 := by simpa [ETag.app] using hb
      exact appG_spec C hok hcode n ih' h h4 (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])
        (by simp +decide [ctxEnv] <;> rfl) (by simp +decide [ctxEnv] <;> rfl) (by simp +decide [ctxEnv])
    · exact leafG_spec (ctxOK_H hok H)

end

end ConPanqueque.T.ExG
