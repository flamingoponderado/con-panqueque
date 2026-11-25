import ConPanqueque.T.Ind.Split

/-!
# The member a name names

`names.findIdx? (· == n)` over a block's member names (its first `k` records' names): `nameIdx(p, j, k, n)` is
the first index from `j` below `k` whose record is named `n`, `k` when none (`nameIdxP`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- The first index from `j` below `k` whose record is named `n` (`k` if none). -/
def nameIdxP (blk : List IConstantInfo) (k : Nat) (n : NIdx) : Nat → Nat → Nat
  | 0, _ => k
  | fuel + 1, j => if j < k then
      match blk[j]? with
      | some ci => if ci.name = n then j else nameIdxP blk k n fuel (j + 1)
      | none => k
    else k

theorem nameIdxP_eq (blk : List IConstantInfo) (k : Nat) (hk : k ≤ blk.length) (n : NIdx) :
    ∀ fuel j, k - j ≤ fuel → j ≤ k →
      nameIdxP blk k n fuel j = ((((blk.take k).drop j).map (·.name)).findIdx? (· == n)).elim k (j + ·) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j h hj
    have : j = k := by omega
    subst this
    simp [nameIdxP]
  | succ f ih =>
    intro j h hj
    by_cases hjk : j < k
    · have hjl : j < blk.length := by omega
      simp only [nameIdxP, ite_eq_left hjk, List.getElem?_eq_getElem hjl]
      have hd : (blk.take k).drop j = blk[j] :: (blk.take k).drop (j + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
      rw [hd, List.map_cons, List.findIdx?_cons]
      by_cases he : blk[j].name = n
      · simp [he]
      · rw [ite_eq_right he, ih (j + 1) (by omega) (by omega)]
        have : (blk[j].name == n) = false := by simpa using he
        simp only [this, Bool.false_eq_true, ite_false]
        cases (List.findIdx? (fun x => x == n) (List.map (fun x => x.name) (List.drop (j + 1) (List.take k blk)))) <;>
          simp [Option.elim]; omega
    · have : j = k := by omega
      subst this
      cases f <;> simp [nameIdxP]

def niP := ofString "ni_p"
def niJ := ofString "ni_j"
def niK := ofString "ni_k"
def niN := ofString "ni_n"
def niQ := ofString "ni_q"
def niW := ofString "ni_w"
def niR := ofString "ni_r"
def fNameIdx := ofString "nameIdx"

def niParams : List MlS := [niP, niJ, niK, niN]
def niLocals : List MlS := [niQ, niW, niR]

def niBody : ProgHOL 64 := prologue niLocals
  (.ite (.cmp .lower (vv niJ) (vv niK))
    (.seq (.assign .local niQ (.load .one (.op .add [vv niP, .op .add [.panop .mul [vv niJ, .const 8], .const 8]])))
    (.seq (.assign .local niW (.load .one (.op .add [vv niQ, .const 8])))
    (.ite (.cmp .equal (vv niW) (vv niN)) (.return (vv niJ))
      (.seq (.call (some (some (.local, niR), none)) fNameIdx [vv niP, .op .add [vv niJ, .const 1], vv niK, vv niN])
        (.return (vv niR))))))
    (.return (vv niK)))

section
variable {σ : Type}

theorem ni_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ niLocals → (ctxEnv C ++ niParams.zip vals).get x = none :=
  Knot.params_none C niLocals niParams vals (by decide) (by decide)

theorem cie_name {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    H[o + 1]? = some (Enc.idxW ci.name) := by
  obtain ⟨hcv, -⟩ := h
  have := hcv.1
  cases ci <;> exact this

/-- **`nameIdx`**: the member named `n` from index `j`. -/
theorem ni_spec (C : Ctx) (hc : C.code.lookup fNameIdx = some (niParams.map (fun p => (p, ShapeHOL.one)), niBody, .one))
    (blk : List IConstantInfo) (ob k : Nat) (n : NIdx) (hk : k ≤ blk.length) (hlen : blk.length < 2 ^ 59) :
    ∀ f j (H : List (BitVec 64)) (s : AState), C.H <+: H → IndBlk C H ob blk → k - j = f → j ≤ k →
      SpecR (σ := σ) (Pre (ctxH C H) s (niParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 k,
        Enc.idxW n])) niBody s (pure (nameIdxP blk k n f j)) (PostN (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hp hb hf hj
    have hjk : j = k := by omega
    subst hjk
    refine specR_prologue (postN_locals _) (ni_none _ _) ?_
    have hlw := nd_lt_iff j j (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, niParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ (BitVec.ofNat 64 j) (by simp +decide [sev, Env.get, niParams, ctxEnv])
      (fun t' ht' => ⟨H, List.prefix_refl _, by simp [nameIdxP], sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hp hb hf hj
    have hjk : j < k := by omega
    have hjl : j < blk.length := by omega
    obtain ⟨os, hosl, hblk, hcie⟩ := id hb
    have hoj : j < os.length := by omega
    refine specR_prologue (postN_locals _) (ni_none _ _) ?_
    have hlw := nd_lt_iff j k (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, niParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjk])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : (ctxH C H).H[ob + 1 + j]? = some (cellA C os[j]) := by
      show H[ob + 1 + j]? = _
      have := hblk.2 j (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) niQ _ (ob + 1 + j) _ hw (by decide)
      (by simp +decide [sev, Env.get, niParams, ctxEnv]; exact cellA_mulIdx C ob j (by omega)) ?_
    have hnm := cie_name (hcie j hjl hoj)
    refine UD.specR_heapLoadI' (C := ctxH C H) niW _ (os[j] + 1) _ hnm (by decide)
      (by simp [sev, Env.get_cons]; exact cellA_plus C os[j] 1) ?_
    simp only [nameIdxP, ite_eq_left hjk, List.getElem?_eq_getElem hjl]
    have hcmp : sev ((niW, Enc.idxW blk[j].name) :: (niQ, cellA C os[j]) :: (ctxEnv (ctxH C H) ++
        niParams.zip [cellA C ob, BitVec.ofNat 64 j, BitVec.ofNat 64 k, Enc.idxW n]))
        (.cmp .equal (vv niW) (vv niN)) = some (if blk[j].name = n then 1 else 0) := by
      simp +decide [sev, Env.get, niParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      by_cases e : blk[j].name = n
      · simp [e]
      · have : Enc.idxW blk[j].name ≠ Enc.idxW n := fun h => e (ConPanqueque.V.Enc.idxW_inj h)
        simp [e, this]
    by_cases he : blk[j].name = n
    · refine specR_ifI _ _ hcmp (fun _ => ?_) (fun h => by simp [he] at h)
      rw [ite_eq_left he]
      exact specR_returnI _ (BitVec.ofNat 64 j) (by simp +decide [sev, Env.get, niParams, ctxEnv])
        (fun t' ht' => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ _ hcmp (fun h => by simp [he] at h) (fun _ => ?_)
      rw [ite_eq_right he]
      refine specR_congr (m' := (pure (nameIdxP blk k n f (j + 1)) : AM Nat) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) niR fNameIdx niParams [vv niP, .op .add [vv niJ, .const 1], vv niK, vv niN]
        niBody [cellA C ob, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 k, Enc.idxW n] (by decide) rfl
        (by simp +decide [ctxLocals, niLocals]) hc
        ⟨by simp +decide [sev, Env.get, niParams, ctxEnv], by simp +decide [sev, Env.get, niParams, ctxEnv]; exact word_add1_eq j,
          by simp +decide [sev, Env.get, niParams, ctxEnv], by simp +decide [sev, Env.get, niParams, ctxEnv], trivial⟩
        (PostN (ctxH C H)) (fun r w _ _ => w = BitVec.ofNat 64 r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu niParams _ rfl hlk)
          (ih (j + 1) H s hp hb (by omega) (by omega)))
        (fun r w s1 H1 hp1 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp +decide [Env.get])
        (fun t' ht' => ⟨H1, hp1, rfl, sr_of_eq ht'.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
