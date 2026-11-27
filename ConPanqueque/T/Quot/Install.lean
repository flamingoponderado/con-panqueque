import ConPanqueque.T.Decl.Install

/-!
# Installing a quotient constant (ten words)

`instQBody`: `instBody` with a ten-word constant block `[tag, name, lps, type, w₄ … w₉]`, room for an
inductive type's or a constructor's fields (`CIE`). The constant value is read from a value-heap record
`[name, lps, type]`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Decl

/-- Stores `x + 8 (i + j) := es[j]`, then `rest`. -/
def envStoresP (x : MlS) : List (ExpHOL 64) → Nat → ProgHOL 64 → ProgHOL 64
  | [], _, rest => rest
  | e :: es, i, rest => .seq (.store (.op .add [vv x, .const (BitVec.ofNat 64 (8 * i))]) e) (envStoresP x es (i + 1) rest)

section
variable {σ : Type}

/-- **A run of environment-heap stores** at fresh cells from `b + i` on. -/
theorem specR_envStoresI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (b : Nat)
    (hx : Γ.get x = some (ecell C b)) (hb : C.EH.length ≤ b) :
    ∀ (es : List (ExpHOL 64)) (vs : List (BitVec 64)) (i : Nat) (E : List (BitVec 64)) (M : Mem),
      C.EH <+: E → b + i + es.length ≤ E.length → EvAll (fun e v => sev Γ e = some v) es vs →
      (∀ E', C.EH <+: E' → E'.length = E.length → (∀ p, p < b + i → E'[p]? = E[p]?) →
        (∀ j (hj : j < vs.length), E'[b + i + j]? = some vs[j]) → SpecR (Inv (ctxE C E') s Γ [] D) rest s m R) →
      SpecR (Inv (ctxE C E) s Γ M D) (envStoresP x es i rest) s m R := by
  intro es
  induction es with
  | nil =>
    intro vs i E M hp hl hev hk
    cases vs with
    | cons _ _ => exact hev.elim
    | nil =>
      intro t ht
      exact hk E hp rfl (fun _ _ => rfl) (fun j hj => absurd hj (by simp)) t
        ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  | cons e es ih =>
    intro vs i E M hp hl hev hk
    cases vs with
    | nil => exact hev.elim
    | cons v vs =>
      obtain ⟨hv, hev'⟩ := hev
      simp only [envStoresP]
      have hj : b + i < E.length := by simp at hl; omega
      refine specR_envStoreI (C := ctxE C E) (ctxOK_E hok hp) _ e (b + i) hj v
        (by simp only [sev, sev_vv, hx, ctxE]; simp; exact ecell_addk C b i) hv ?_
      refine ih vs (i + 1) (E.set (b + i) v) [] (prefix_set_ge hp _ (by omega) v) (by simp at hl ⊢; omega) hev'
        (fun E' hp' hl' hlo hj' => hk E' hp' (by simpa using hl') (fun p hpb => ?_) (fun j hjl => ?_))
      · rw [hlo p (by omega), List.getElem?_set_ne (by omega)]
      · rcases j with _ | j
        · have := hlo (b + i) (by omega)
          rw [List.getElem?_set_self hj] at this
          simpa using this
        · have := hj' j (by simp at hjl; omega)
          rw [show b + (i + 1) + j = b + i + (j + 1) by omega] at this
          simpa using this

end

/-- What `EnvDen` asks of a new recursor's rules. -/
def RulesDen (ci : IConstantInfo) (st : EStore) : Prop :=
  ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ rl ∈ rules,
    (∀ lv, ((∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv) →
      (∀ u ∈ lv, (denoteL st.ls u).isSome = true) ∧ lv.length < 2 ^ 61) ∧
    (∀ lv pins, rl.fire = .nested lv pins → ∀ p ∈ pins, (denoteE st p).isSome = true)

theorem envDen_pushR {fe fe' : IFEnv} {p : Pins} {st : EStore} {ci : IConstantInfo}
    (hf : ∀ n, fe'.find? n = if (ci.name == n) = true then some ci else fe.find? n)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) (hnew : NewDen ci st)
    (hrd : RulesDen ci st) : EnvDen fe' p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  refine ⟨fun c ci' hci => ?_, fun T tbl h' => htb T tbl (by rw [← ht]; exact h'), hp,
    fun c cv mI rP isK rules hci => ?_⟩
  · rw [hf] at hci
    split at hci
    · cases hci; exact hnew
    · exact hc c ci' hci
  · rw [hf] at hci
    split at hci
    · cases hci; exact hrd cv mI rP isK rules rfl
    · exact hr c cv mI rP isK rules hci

def iqT := ofString "iq_t"
def iqQ := ofString "iq_q"
def iq4 := ofString "iq_4"
def iq5 := ofString "iq_5"
def iq6 := ofString "iq_6"
def iq7 := ofString "iq_7"
def iq8 := ofString "iq_8"
def iq9 := ofString "iq_9"
def iqN := ofString "iq_n"
def iqL := ofString "iq_l"
def iqTy := ofString "iq_ty"
def iqLn := ofString "iq_ln"
def iqB := ofString "iq_b"
def iqX := ofString "iq_x"
def iqR := ofString "iq_r"
def fInstQ := ofString "installQuot"

def iqParams : List MlS := [iqT, iqQ, iq4, iq5, iq6, iq7, iq8, iq9]
def iqLocals : List MlS := [iqN, iqL, iqTy, iqLn, iqB, iqX, iqR]

/-- Install: the level-parameter block and the ten-word constant block in fresh environment cells, then the
name into the constant table. -/
def instQBody (C : Ctx) : ProgHOL 64 := prologue iqLocals
  (.seq (.assign .local iqN (.load .one (vv iqQ)))
  (.seq (.assign .local iqL (.load .one (.op .add [vv iqQ, .const 8])))
  (.seq (.assign .local iqTy (.load .one (.op .add [vv iqQ, .const 16])))
  (.seq (.assign .local iqLn (.load .one (vv iqL)))
  (envAllocP C iqB (.op .add [.panop .mul [vv iqLn, .const 8], .const 8])
  (.seq (.store (vv iqB) (vv iqLn))
  (.seq (.call (some (some (.local, iqR), none)) fCpy [vv iqL, vv iqB, .const 0, vv iqLn])
  (envAllocP C iqX (.const 80)
  (envStoresP iqX [vv iqT, vv iqN, vv iqB, vv iqTy, vv iq4, vv iq5, vv iq6, vv iq7, vv iq8, vv iq9] 0
  (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv iqN))
  (.seq (.call (some (some (.local, iqR), none)) fMemoSet [.const (C.mG .env), .const 1, vv iqX])
  (.return (vv iqX)))))))))))))

/-- The ten words of an installed constant block, and its level-parameter block. -/
def Lay10 (C : Ctx) (EH : List (BitVec 64)) (ox b : Nat) (ws : List (BitVec 64)) (ci : IConstantInfo) : Prop :=
  EH[ox + 1]? = some (Enc.idxW ci.name) ∧ EH[ox + 2]? = some (ecell C b) ∧
    EH[ox + 3]? = some (Enc.idxW ci.toConstantVal.type) ∧ (∀ j (hj : j < ws.length), EH[ox + j]? = some ws[j]) ∧
    EBlk EH b (ci.toConstantVal.levelParams.map Enc.idxW)

section
variable {σ : Type}

theorem iq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ iqLocals → (ctxEnv C ++ iqParams.zip vals).get x = none :=
  Knot.params_none C iqLocals iqParams vals (by decide) (by decide)

/-- **Install** a quotient constant (not a recursor) whose name is fresh. -/
theorem instQ_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (s : AState) (ci : IConstantInfo) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW ci.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW ci.toConstantVal.type))
    (hb : BlkAt C.H o (ci.toConstantVal.levelParams.map Enc.idxW)) (hlen : ci.toConstantVal.levelParams.length < 2 ^ 60)
    (tW w4 w5 w6 w7 w8 w9 : BitVec 64)
    (hcie : ∀ EH ox b, C.EH <+: EH → Lay10 C EH ox b [tW, Enc.idxW ci.name, ecell C b,
      Enc.idxW ci.toConstantVal.type, w4, w5, w6, w7, w8, w9] ci → CIE C.EB EH ox ci)
    (hg : TblGate C.fe) (hnew : C.fe.find? ci.name = none) (hden : NewDen ci s.store)
    (hrd : RulesDen ci s.store) :
    SpecR (σ := σ) (Pre C s (iqParams.zip [tW, cellA C q, w4, w5, w6, w7, w8, w9])) (instQBody C) s
      (pure (C.fe.push ci)) (PostInst C ci) := by
  refine specR_prologue (postInst_locals C ci) (iq_none C _) ?_
  set lps := ci.toConstantVal.levelParams with hlps
  refine UD.specR_heapLoadI' (C := C) iqN _ q _ hn (by decide) (by simp +decide [Env.get, iqParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) iqL _ (q + 1) _ hl (by decide)
    (by simp +decide [sev, Env.get, iqParams, ctxEnv]; exact cellA_add8 C q) ?_
  refine UD.specR_heapLoadI' (C := C) iqTy _ (q + 2) _ ht (by decide)
    (by simp +decide [sev, Env.get, iqParams, ctxEnv]; exact cellA_add_ofNat C q 2) ?_
  have hb1 : C.H[o]? = some (BitVec.ofNat 64 lps.length) := by simpa using hb.1
  refine UD.specR_heapLoadI' (C := C) iqLn _ o _ hb1 (by decide) (by simp +decide [Env.get]) ?_
  -- the level-parameter block
  refine specR_envAllocI iqB _ (lps.length + 1) (by omega) (by decide)
    (fun v => by simp +decide [sev, Env.get]; exact len8_eq lps.length) (fun ws1 hws1 hroom1 => ?_)
  have hp1 : C.EH <+: C.EH ++ ws1 := List.prefix_append _ _
  have hj1 : C.EH.length < (ctxE C (C.EH ++ ws1)).EH.length := by show _ < (C.EH ++ ws1).length; simp; omega
  refine specR_envStoreI (ctxOK_E hok hp1) (vv iqB) (vv iqLn) C.EH.length hj1 (BitVec.ofNat 64 lps.length)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  have hp2 : C.EH <+: (C.EH ++ ws1).set C.EH.length (BitVec.ofNat 64 lps.length) :=
    prefix_set_ge hp1 C.EH.length (le_refl _) _
  have hE2len : ((C.EH ++ ws1).set C.EH.length (BitVec.ofNat 64 lps.length)).length = C.EH.length + (lps.length + 1) := by
    simp [hws1]
  -- copy the names
  set E2 := (C.EH ++ ws1).set C.EH.length (BitVec.ofNat 64 lps.length) with hE2
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure (C.fe.push ci)) rfl ?_
  refine specR_callNC (C := ctxE C E2) (D := ctxLocals ++ iqLocals) iqR fCpy cpParams
    [vv iqL, vv iqB, .const 0, vv iqLn] cpyBody
    [cellA C o, ecell C C.EH.length, BitVec.ofNat 64 0, BitVec.ofNat 64 (lps.map Enc.idxW).length]
    (by decide) rfl (by decide) hcp ?_ (fun a w s' st => PostCp C C.EH.length (lps.map Enc.idxW) 0 E2 a w s' st ∧ s' = s)
    (fun _ w s' C' => s' = s ∧ ∃ EH', C' = ctxE C EH' ∧ EH'.length = E2.length ∧
      (∀ p, p < C.EH.length + 1 + 0 → EH'[p]? = E2[p]?) ∧
      (∀ j (hj : j < (lps.map Enc.idxW).length), 0 ≤ j → EH'[C.EH.length + 1 + j]? = some (lps.map Enc.idxW)[j]))
    (fun a w s' st ⟨⟨EH', h1, h2, h3, h4⟩, hs⟩ => ⟨ctxE C EH', ⟨hs, EH', rfl, h1, h2, h3⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cpParams _ rfl hlk)
      (specR_pureState (cpy_spec C hok hcp o C.EH.length (lps.map Enc.idxW) hb (le_refl _) (by simp; omega) s _ 0 E2
        hp2 (by simp [hE2len]; omega) rfl (Nat.zero_le _))))
    (fun _ w s3 C3 ⟨hs3, E3, eC, h1, h2, h3⟩ => ?_)
  · exact ⟨by simp +decide [Env.get, iqParams, ctxEnv] <;> rfl, by simp +decide [Env.get], rfl,
      by simp +decide [Env.get], trivial⟩
  subst eC hs3
  have hp3 : C.EH <+: E3 := by
    refine List.prefix_iff_eq_take.mpr ?_
    apply List.ext_getElem?
    intro p
    by_cases hpl : p < C.EH.length
    · rw [List.getElem?_take, ite_eq_left hpl, h2 p (by omega), List.getElem?_eq_getElem hpl,
        get_prefix (List.getElem?_eq_getElem hpl) hp2]
    · rw [List.getElem?_take, ite_eq_right hpl, List.getElem?_eq_none (by omega)]
  -- the constant block
  refine specR_envAllocI iqX (.const 80) 10 (by omega) (by decide) (fun v => rfl) (fun ws2 hws2 hroom2 => ?_)
  have hp4 : C.EH <+: E3 ++ ws2 := hp3.trans (List.prefix_append _ _)
  have hE3l : E3.length = C.EH.length + (lps.length + 1) := by rw [h1, hE2len]
  let ws : List (BitVec 64) := [tW, Enc.idxW ci.name, ecell C C.EH.length, Enc.idxW ci.toConstantVal.type,
    w4, w5, w6, w7, w8, w9]
  refine specR_envStoresI (C := C) hok iqX E3.length (by simp [Env.get_cons]; rfl)
    (by have := hp3.length_le; omega) _ ws 0 (E3 ++ ws2) _ hp4 (by simp [hws2])
    ⟨by simp +decide [Env.get, iqParams, ctxEnv], by simp +decide [Env.get],
      by simp +decide [Env.get] <;> rfl, by simp +decide [Env.get],
      by simp +decide [Env.get, iqParams, ctxEnv], by simp +decide [Env.get, iqParams, ctxEnv],
      by simp +decide [Env.get, iqParams, ctxEnv], by simp +decide [Env.get, iqParams, ctxEnv],
      by simp +decide [Env.get, iqParams, ctxEnv], by simp +decide [Env.get, iqParams, ctxEnv], trivial⟩
    (fun E4 hpE hl4 hlo4 hj4 => ?_)
  have hlay : Lay10 C E4 E3.length C.EH.length ws ci := by
    refine ⟨hj4 1 (by simp [ws]), hj4 2 (by simp [ws]), hj4 3 (by simp [ws]), fun j hj => by simpa using hj4 j hj,
      ?_, fun j hj => ?_⟩
    · rw [hlo4 _ (by omega), List.getElem?_append_left (by omega), h2 _ (by omega), hE2]
      simp [hws1, hlps]
    · have h1' := hE3l
      simp only [hlps] at h1'
      simp only [List.length_map] at hj
      rw [hlo4 _ (by omega), List.getElem?_append_left (by omega)]
      exact h3 j (by simpa using hj) (Nat.zero_le _)
  have hcie' := hcie E4 E3.length C.EH.length hpE hlay
  -- the key, then the table
  refine specR_storeKBI (ctxOK_E hok hpE) 0 (by decide) (vv iqN) (Enc.idxW ci.name) (by simp +decide [Env.get])
    (by simp +decide [Env.get, iqParams, ctxEnv] <;> rfl) ?_
  set fe' := (C.fe.push ci).setFlags C.fe.natLit C.fe.strLit with hfe'
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure (C.fe.push ci)) rfl ?_
  refine specR_memoSetGIC (C := ctxE C E4) (C' := ctxIns C fe' E4 (C.envM.insert ci.name (ecell C E3.length)))
    (D := ctxLocals ++ iqLocals)
    (K := NIdx) (V := BitVec 64) encNI_inj (C.mG .env) (C.mg .env) C.envM ci.name (ecell C E3.length) (pure ()) rfl
    (fun u hu => hu.env.2.1) (fun i hi => hok.kbMemo .env i (by simp [encNI] at hi; omega))
    (fun j hj => hok.mdescMemo .env .env j hj)
    (fun u u' hsr hmem hfr hd hg' hc => sr_envIns (ctxOK_E hok hpE) hsr hfr hd hg' hc hmem rfl
      (envDen_pushR (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew) hsr.envd hden hrd))
    hcS hcI iqR (.const (C.mG .env)) (.const 1) (vv iqX) (by decide) ?_ ?_ ?_
    (by simp [encNI]) (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW ci.name) (by simp)) (fun w => ?_)
  · rfl
  · rfl
  · simp +decide [Env.get] <;> rfl
  try simp only [pure_bind]
  exact specR_returnI _ (ecell C E3.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨E4, E3.length, hpE, hcie', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Quot
