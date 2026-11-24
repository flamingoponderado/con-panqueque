import ConPanqueque.Start.PinCtx

/-! # The pin phase

`pinsP`: two environment blocks (the pin block at cell 64, the reserved names' block at 121),
the 52 pinned names and the 16 reserved names interned into them, then the empty level list, the
level zero (a hit), its successor and `Sort 1`, each stored into the pin block.  `pins_spec`: it
refines con-ron's `internReservedPins`, and ends in the context `C1` of the installed pins. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front

variable {σ : Type}

set_option maxRecDepth 100000

def vRs := ofString "prs"

def ecb (b : Nat) : BitVec 64 := BitVec.ofNat 64 (base + E0) + BitVec.ofNat 64 (8 * b)

theorem ecell_Cb (code : Code) (H EH : List (BitVec 64)) (b : Nat) : ecell (Cb code H EH) b = ecb b := rfl

theorem envAllocP_congr {C C' : Ctx} (h1 : C.EB = C'.EB) (h2 : C.EN = C'.EN) (x : MlS) (e : ExpHOL 64) (r : ProgHOL 64) :
    envAllocP C x e r = envAllocP C' x e r := by unfold envAllocP; rw [h1, h2]

/-- The level zero is a hit once it is interned: the handle word 0, the state unchanged. -/
theorem zero_probe {s : AState} (hok : StateOK s) (hd : denoteL s.store.ls default = some .zero) :
    internLNode .zero s = .ok (default, s) := by
  have hv := view_of_denoteL_zero hd
  obtain ⟨rk, hrk⟩ := hok.wf
  obtain ⟨rkl, hl⟩ := hrk.lss.ls
  have hf := (hl.consP .zero default).mpr ⟨hv, by decide⟩
  have hf' : s.store.ls.pers.find? .zero = some default := hf
  simp [internLNode, LStore.find?, hf', bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, Except.bind]

/-- A store into the environment heap of the bootstrap family. -/
theorem specR_cbStore {α : Type} {code : Code} {H EH : List (BitVec 64)} (hEH : ∀ j, j < 64 → EH[j]? = EH0[j]?)
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (ea ev : ExpHOL 64) (j : Nat) (hj : j < EH.length)
    (w : BitVec 64) (hea : sev Γ ea = some (ecb j)) (hev : sev Γ ev = some w)
    (h : SpecR (Inv (Cb code H (EH.set j w)) s Γ [] D) rest s m R) :
    SpecR (Inv (Cb code H EH) s Γ M D) (.seq (.store ea ev) rest) s m R :=
  specR_envStoreI (ctxOK_Cb code H EH hEH) ea ev j (by rw [Cb_EH]; exact hj) w hea hev (by rw [ctxE_Cb, Cb_EH]; exact h)

theorem sev_off (Γ : Env) (x : MlS) (b i : Nat) (h : Γ.get x = some (ecb b)) :
    sev Γ (.op .add [vv x, .const (BitVec.ofNat 64 (8 * i))]) = some (ecb (b + i)) := by
  simp only [sev, vv, h, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1; unfold ecb; rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.mul_add]

/-- The pin phase. -/
def pinsP (C : Ctx) (rest : ProgHOL 64) : ProgHOL 64 :=
  envAllocP C vPb (.const (BitVec.ofNat 64 (8 * 57)))
  (envAllocP C vRs (.const (BitVec.ofNat 64 (8 * 17)))
  (namesP C vPb pinCss 0
  (namesP C vRs resCss 1
  (.seq (.store (vv vRs) (.const 16))
  (allocP C vKa (.const 0)
  (.seq (.call (some (some (.local, vPn), none)) fInternLs [vv vKa, .const 0])
  (.seq (.store (.op .add [vv vPb, .const (BitVec.ofNat 64 (8 * 52))]) (vv vPn))
  (.seq (.call (some (some (.local, vPn), none)) fInternLZero [])
  (.seq (.store (.op .add [vv vPb, .const (BitVec.ofNat 64 (8 * 53))]) (vv vPn))
  (.seq (.call (some (some (.local, vPn), none)) fInternLSucc [vv vPn])
  (.seq (.call (some (some (.local, vPn), none)) fInternSort [vv vPn])
  (.seq (.store (.op .add [vv vPb, .const (BitVec.ofNat 64 (8 * 54))]) (vv vPn))
  (.seq (.store (.op .add [vv vPb, .const (BitVec.ofNat 64 (8 * 55))]) (.const (BitVec.ofNat 64 maxNatSizeDefault)))
  (.seq (.store (.op .add [vv vPb, .const (BitVec.ofNat 64 (8 * 56))]) (vv vRs))
    rest))))))))))))))

structure PinCodes (code : Code) : Prop where
  nstr : code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one)
  ls : code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  zero : code.lookup fInternLZero = some ([], internLZeroBody, .one)
  succ : code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  sort : code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)

def pinsOf (hs rs : List NIdx) (us : LsIdx) (z : LIdx) (s1 : EIdx) : Pins :=
  { names := hs.toArray, reserved := rs, emptyLevels := us, zeroLevel := z, sortOne := s1,
    maxNatSize := maxNatSizeDefault }

theorem EH0_length' : EH0.length = 64 := EH0_length

set_option maxHeartbeats 4000000 in
/-- **The pin phase refines `internReservedPins`.** -/
theorem pins_spec {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (code : Code) (pc : PinCodes code)
    (D : List MlS) (hD : ∀ x ∈ [vPn, vKa, vPb, vRs], x ∈ D) {rest : ProgHOL 64}
    {R : β → BitVec 64 → AState → PState σ → Prop} (H : List (BitVec 64)) (s : AState) (Γ : Env) (M : Mem)
    (k : Unit → AM β)
    (hk : ∀ sP (EH' : List (BitVec 64)) (Γ' : Env), internReservedPins s = .ok ((), sP) → PinBlock EH' sP.pins →
      sP.pins.zeroLevel = default → (∀ y, y ∉ [vPn, vKa, vPb, vRs] → Γ'.get y = Γ.get y) →
      SpecR (Inv (C1 code H EH' sP.pins) sP Γ' [] D) rest sP (k ()) R) :
    SpecR (Inv (Cb code H EH0) s Γ M D) (pinsP (Cb code H EH0) rest) s (internReservedPins >>= k) R := by
  have hPn := hD vPn (by simp); have hKa := hD vKa (by simp); have hPb := hD vPb (by simp)
  have hRs := hD vRs (by simp)
  simp only [internReservedPins, bind_assoc]
  unfold pinsP
  -- the pin block
  refine specR_envAllocI vPb _ 57 (by decide) hPb (fun v => rfl) (fun ws1 hws1 hroom1 => ?_)
  rw [ctxE_Cb]
  rw [Cb_EH, EH0_length'] at *
  let EH1 := EH0 ++ ws1
  have hl1 : EH1.length = 121 := by simp [EH1, EH0_length', hws1]
  rw [envAllocP_congr (C := Cb code H EH0) (C' := Cb code H EH1) rfl rfl]
  -- the reserved names' block
  refine specR_envAllocI vRs _ 17 (by decide) hRs (fun v => rfl) (fun ws2 hws2 hroom2 => ?_)
  rw [ctxE_Cb, Cb_EH]
  let EH2 := EH1 ++ ws2
  have hl2 : EH2.length = 138 := by simp [EH2, hl1, hws2]
  have hEH2 : ∀ j, j < 64 → EH2[j]? = EH0[j]? := fun j hj => by
    simp only [EH2, EH1, List.append_assoc]; rw [List.getElem?_append_left (by rw [EH0_length']; omega)]
  let Γ2 : Env := (vRs, ecell (Cb code H EH1) EH1.length) :: (vPb, ecell (Cb code H EH0) 64) :: Γ
  have g2pb : Γ2.get vPb = some (ecb 64) := by simp [Γ2, T.Env.get_cons, show vPb ≠ vRs by decide]; rfl
  have g2rs : Γ2.get vRs = some (ecb 121) := by simp [Γ2, T.Env.get_cons, hl1]; rfl
  rw [namesP_congr (C := Cb code H EH0) (C' := Cb code H EH2) rfl rfl]
  -- the 52 pinned names
  refine names_spec ra code pc.nstr D hPn hKa H 64 (by decide) vPb (by decide) (by decide) pinNames pinCss 0 EH2
    s Γ2 M _ pinCss_ok hEH2 (by rw [ecell_Cb]; exact g2pb) (by rw [pinNames_length, hl2]; decide)
    (fun hs s1 EH3 Γ3 hl3 hag3a hc3 hag3 hr1 => ?_)
  have hhs : hs.length = 52 := by rw [internNameList_length _ _ _ _ hr1, pinNames_length]
  have hEH3 : ∀ j, j < 64 → EH3[j]? = EH0[j]? := fun j hj => by rw [hag3a j (by omega)]; exact hEH2 j hj
  have g3rs : Γ3.get vRs = some (ecb 121) := by rw [hag3 _ (by decide) (by decide)]; exact g2rs
  have g3pb : Γ3.get vPb = some (ecb 64) := by rw [hag3 _ (by decide) (by decide)]; exact g2pb
  rw [namesP_congr (C := Cb code H EH0) (C' := Cb code H EH3) rfl rfl]
  -- the 16 reserved names
  refine names_spec ra code pc.nstr D hPn hKa H 121 (by decide) vRs (by decide) (by decide) reservedBasisNameValues
    resCss 1 EH3 s1 Γ3 [] _ resCss_ok hEH3 (by rw [ecell_Cb]; exact g3rs) (by rw [reserved_length, hl3, hl2])
    (fun rs s2 EH4 Γ4 hl4 hag4a hc4 hag4 hr2 => ?_)
  have hrs : rs.length = 16 := by rw [internNameList_length _ _ _ _ hr2, reserved_length]
  have hEH4 : ∀ j, j < 64 → EH4[j]? = EH0[j]? := fun j hj => by rw [hag4a j (by omega)]; exact hEH3 j hj
  have g4rs : Γ4.get vRs = some (ecb 121) := by rw [hag4 _ (by decide) (by decide)]; exact g3rs
  have g4pb : Γ4.get vPb = some (ecb 64) := by rw [hag4 _ (by decide) (by decide)]; exact g3pb
  have hl4' : EH4.length = 138 := by rw [hl4, hl3, hl2]
  -- the reserved block's count
  refine specR_cbStore hEH4 (vv vRs) (.const 16) 121 (by omega) 16 (by simpa [sev, vv] using g4rs) rfl ?_
  let EH5 := EH4.set 121 16
  have hEH5 : ∀ j, j < 64 → EH5[j]? = EH0[j]? := fun j hj => by
    simp only [EH5]; rw [List.getElem?_set, if_neg (by omega)]; exact hEH4 j hj
  -- an empty key for the empty level list
  rw [allocP_congr (C := Cb code H EH0) (C' := Cb code H EH5) rfl rfl]
  refine specR_allocI vKa _ 0 (by decide) hKa (fun v => rfl) (fun H' ws hpre hwl hcapH => ?_)
  rw [ctxH_Cb]
  have hws : ws = [] := List.eq_nil_of_length_eq_zero hwl
  subst hws
  have hpre' : H <+: H' ++ [] := by rw [List.append_nil]; exact hpre
  have hHl : H.length ≤ H'.length := hpre.length_le
  let Γ6 : Env := (vKa, cellA (Cb code H EH5) H'.length) :: Γ4
  -- the empty level list
  refine specR_callPost vPn fInternLs [pKey, lEc] [vv vKa, .const 0] internLsBody
    [cellA (Cb code (H' ++ []) EH5) H'.length, BitVec.ofNat 64 0] (by decide) rfl hPn (by rw [Cb_code]; exact pc.ls)
    ⟨by simp [sev, vv, T.Env.get_cons]; rfl, rfl, trivial⟩ Enc.idxW H
    (internLs_body_spec (σ := σ) ra (Cb code (H' ++ []) EH5) (ctxOK_Cb code _ EH5 hEH5) s2 [] H'.length H hpre'
      hHl (by simp [Cb_H]) (by decide) (fun j hj => absurd hj (by simp))) (fun us s7 hr7 => ?_)
  rw [ctxH_Cb]
  have g7pb : T.Env.get ((vPn, Enc.idxW us) :: Γ6) vPb = some (ecb 64) := by
    simp only [Γ6, T.Env.get_cons, show vPb ≠ vPn by decide, show vPb ≠ vKa by decide, if_false]; exact g4pb
  refine specR_cbStore hEH5 _ (vv vPn) (64 + 52) (by simp [EH5, hl4']) (Enc.idxW us) (sev_off _ vPb 64 52 g7pb)
    (by simp [sev, vv, T.Env.get_cons]) ?_
  let EH6 := EH5.set (64 + 52) (Enc.idxW us)
  have hEH6 : ∀ j, j < 64 → EH6[j]? = EH0[j]? := fun j hj => by
    simp only [EH6]; rw [List.getElem?_set, if_neg (by omega)]; exact hEH5 j hj
  -- the level zero (a hit)
  intro t7 ht7
  have hst7 : StateOK s7 := ⟨ht7.sr.twf⟩
  have hd7 : denoteL s7.store.ls default = some .zero := denoteL_ext (boot_ok P0).2.2.2.1 ht7.sr.floor
  have hzp := zero_probe hst7 hd7
  refine specR_callPost vPn fInternLZero [] [] internLZeroBody [] List.nodup_nil rfl hPn (by rw [Cb_code]; exact pc.zero)
    trivial Enc.idxW H (internLZero_body_spec (σ := σ) ra (Cb code H EH6) (ctxOK_Cb code H EH6 hEH6) s7)
    (fun z s8 hr8 => ?_) t7 ht7
  rw [hzp] at hr8
  obtain ⟨rfl, rfl⟩ : (default : LIdx) = z ∧ s7 = s8 := by simpa using hr8
  rw [ctxH_Cb]
  let Γ8 : Env := (vPn, Enc.idxW (default : LIdx)) :: (vPn, Enc.idxW us) :: Γ6
  have g8pb : T.Env.get Γ8 vPb = some (ecb 64) := by
    simp only [Γ8, T.Env.get_cons, show vPb ≠ vPn by decide, if_false]; exact g7pb
  refine specR_cbStore hEH6 _ (vv vPn) (64 + 53) (by simp [EH6, EH5, hl4']) (Enc.idxW (default : LIdx))
    (sev_off _ vPb 64 53 g8pb) (by simp [sev, vv, Γ8, T.Env.get_cons]) ?_
  let EH7 := EH6.set (64 + 53) (Enc.idxW (default : LIdx))
  have hEH7 : ∀ j, j < 64 → EH7[j]? = EH0[j]? := fun j hj => by
    simp only [EH7]; rw [List.getElem?_set, if_neg (by omega)]; exact hEH6 j hj
  -- its successor
  refine specR_callPost vPn fInternLSucc [lEu] [vv vPn] internLSuccBody [Enc.idxW (default : LIdx)] (by decide) rfl hPn
    (by rw [Cb_code]; exact pc.succ) ⟨by simp [sev, vv, Γ8, T.Env.get_cons], trivial⟩ Enc.idxW H
    (internLSucc_body_spec (σ := σ) ra (Cb code H EH7) (ctxOK_Cb code H EH7 hEH7) s7 default)
    (fun o s9 hr9 => ?_)
  rw [ctxH_Cb]
  -- `Sort 1`
  refine specR_callPost vPn fInternSort [lEu] [vv vPn] sortBody [Enc.idxW o] (by decide) rfl hPn
    (by rw [Cb_code]; exact pc.sort) ⟨by simp [sev, vv, T.Env.get_cons], trivial⟩ Enc.idxW H
    (sort_body_spec (σ := σ) ra (Cb code H EH7) (ctxOK_Cb code H EH7 hEH7) s9 o)
    (fun s1 s10 hr10 => ?_)
  rw [ctxH_Cb]
  let Γ10 : Env := (vPn, Enc.idxW s1) :: (vPn, Enc.idxW o) :: Γ8
  have g10pb : T.Env.get Γ10 vPb = some (ecb 64) := by
    simp only [Γ10, T.Env.get_cons, show vPb ≠ vPn by decide, if_false]; exact g8pb
  have g10rs : T.Env.get Γ10 vRs = some (ecb 121) := by
    simp only [Γ10, Γ8, Γ6, T.Env.get_cons, show vRs ≠ vPn by decide, show vRs ≠ vKa by decide, if_false]; exact g4rs
  refine specR_cbStore hEH7 _ (vv vPn) (64 + 54) (by simp [EH7, EH6, EH5, hl4']) (Enc.idxW s1)
    (sev_off _ vPb 64 54 g10pb) (by simp [sev, vv, Γ10, T.Env.get_cons]) ?_
  let EH8 := EH7.set (64 + 54) (Enc.idxW s1)
  have hEH8 : ∀ j, j < 64 → EH8[j]? = EH0[j]? := fun j hj => by
    simp only [EH8]; rw [List.getElem?_set, if_neg (by omega)]; exact hEH7 j hj
  refine specR_cbStore hEH8 _ _ (64 + 55) (by simp [EH8, EH7, EH6, EH5, hl4'])
    (BitVec.ofNat 64 maxNatSizeDefault) (sev_off _ vPb 64 55 g10pb) rfl ?_
  let EH9 := EH8.set (64 + 55) (BitVec.ofNat 64 maxNatSizeDefault)
  have hEH9 : ∀ j, j < 64 → EH9[j]? = EH0[j]? := fun j hj => by
    simp only [EH9]; rw [List.getElem?_set, if_neg (by omega)]; exact hEH8 j hj
  refine specR_cbStore hEH9 _ (vv vRs) (64 + 56) (by simp [EH9, EH8, EH7, EH6, EH5, hl4']) (ecb 121)
    (sev_off _ vPb 64 56 g10pb) (by simp only [sev, vv]; exact g10rs) ?_
  let EH10 := EH9.set (64 + 56) (ecb 121)
  -- the twin installs the pins
  let P := pinsOf hs rs us default s1
  let sP : AState := { s10 with pins := P }
  have e : (get >>= fun x6 : AState => set { x6 with pins := P } >>= k) s10 = k () sP := by
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set,
      Except.bind, pure, Except.pure, sP]
  refine specR_congr (m' := fun _ => k () sP) e ?_
  intro t ht
  have hz : denoteL s10.store.ls P.zeroLevel = some .zero := denoteL_ext (boot_ok P0).2.2.2.1 ht.sr.floor
  have hrun : internReservedPins s = .ok ((), sP) := by
    simp only [internReservedPins, bind, StateT.bind, Except.bind, hr1, hr2, hr7, hzp, hr9, hr10, get, getThe,
      MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure]
    rfl
  have sne : ∀ (l : List (BitVec 64)) (a b : Nat) (w : BitVec 64), a ≠ b → (l.set a w)[b]? = l[b]? :=
    fun l a b w h => by rw [List.getElem?_set, if_neg h]
  have sself : ∀ (l : List (BitVec 64)) (a : Nat) (w : BitVec 64), a < l.length → (l.set a w)[a]? = some w :=
    fun l a w h => List.getElem?_set_self h
  have hl5 : EH5.length = 138 := by simp [EH5, hl4']
  have hl6 : EH6.length = 138 := by simp [EH6, hl5]
  have hl7 : EH7.length = 138 := by simp [EH7, hl6]
  have hl8 : EH8.length = 138 := by simp [EH8, hl7]
  have hl9 : EH9.length = 138 := by simp [EH9, hl8]
  have hb : PinBlock EH10 sP.pins := {
    size := by simp [sP, P, pinsOf, hhs, pinCount]
    names := fun i hi => by
      have hi' : i < 52 := by simpa [sP, P, pinsOf, hhs] using hi
      simp only [EH10, EH9, EH8, EH7, EH6, EH5]
      rw [sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega),
        sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), hag4a _ (by omega)]
      have := hc3 i (by rw [pinNames_length]; exact hi')
      rw [Nat.add_zero] at this; rw [this]
      simp [sP, P, pinsOf, List.getElem?_eq_getElem (show i < hs.length by omega)]
    us := by
      simp only [EH10, EH9, EH8, EH7, EH6]
      rw [sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega),
        sself _ _ _ (by omega)]; rfl
    z := by
      simp only [EH10, EH9, EH8, EH7]
      rw [sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sself _ _ _ (by omega)]; rfl
    s1 := by
      simp only [EH10, EH9, EH8]
      rw [sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sself _ _ _ (by omega)]; rfl
    mx := ⟨by simp only [EH10, EH9]; rw [sne _ _ _ _ (by omega), sself _ _ _ (by omega)], rfl⟩
    ptr := by simp only [EH10]; rw [sself _ _ _ (by omega)]; rfl
    cnt := by
      simp only [EH10, EH9, EH8, EH7, EH6, EH5]
      rw [sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega),
        sne _ _ _ _ (by omega), sself _ _ _ (by omega)]
      simp [sP, P, pinsOf, hrs]
    res := fun i hi => by
      have hi' : i < 16 := by simpa [sP, P, pinsOf, hrs] using hi
      simp only [EH10, EH9, EH8, EH7, EH6, EH5]
      rw [sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega), sne _ _ _ _ (by omega),
        sne _ _ _ _ (by omega), sne _ _ _ _ (by omega)]
      have := hc4 i (by rw [reserved_length]; exact hi')
      rw [show 121 + 1 + i = 122 + i by omega] at this; rw [this]
      simp [sP, P, pinsOf, List.getElem?_eq_getElem (show i < rs.length by omega)] }
  have hag : ∀ y, y ∉ [vPn, vKa, vPb, vRs] → T.Env.get Γ10 y = Γ.get y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Γ10, Γ8, Γ6, T.Env.get_cons, if_neg hy.1, if_neg hy.2.1]
    rw [hag4 y hy.1 hy.2.1, hag3 y hy.1 hy.2.1]
    simp only [Γ2, T.Env.get_cons, if_neg hy.2.2.2, if_neg hy.2.2.1]
  exact hk sP EH10 Γ10 hrun hb rfl hag t ⟨sr_switch P ht.sr hz, ht.env, ht.mem, ht.decl⟩

end ConPanqueque.Start
