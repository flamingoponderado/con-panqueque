import ConPanqueque.Start.Main2
import ConPanqueque.Pipeline.Prepare
import ConPanqueque.Pipeline.NameInj

/-! # From name words to names

The pass compares handle words.  With the pin table's denotation (`PinsOK`), persistence, and
canonical handles (`denoteN_inj`), a record whose name word differs from every pinned cell's word
has a name outside `FN`, the pinned names, the reserved names and `Bool.rec` (`name_notMem`). -/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConPanqueque.V ConPanqueque.T

namespace ConPanqueque.Start

def boolRecName : ConLeche.Name := (ConLeche.Name.anonymous.str "Bool").str "rec"

/-- The forbidden names. -/
def FN : List ConLeche.Name := pinNames ++ reservedBasisNameValues ++ [boolRecName]

theorem denoteNL_get {st : EStore} : ∀ {hs : List NIdx} {xs : List ConLeche.Name}, denoteNL st hs xs →
    hs.length = xs.length ∧ ∀ i (hi : i < xs.length) (hi' : i < hs.length), denoteN st.ns hs[i] = some xs[i]
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | h :: hs, x :: xs, ⟨h1, h2⟩ => by
    obtain ⟨hl, hg⟩ := denoteNL_get h2
    refine ⟨by simp [hl], fun i hi hi' => ?_⟩
    cases i with
    | zero => exact h1
    | succ i => exact hg i (by simpa using hi) (by simpa using hi')
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **A checked name word is a name outside `FN`.** -/
theorem name_notMem (st : EStore) (hwf : NStoreWF st.ns) (P : Pins) (EH : List (BitVec 64)) (hb : PinBlock EH P)
    (hdn : denoteNL st P.names.toList pinNames) (hdr : denoteNL st P.reserved reservedBasisNameValues)
    (hpn : ∀ n ∈ P.names, PersN n) (hpr : PersNList P.reserved)
    (bh : NIdx) (hB : EH[138]? = some (Enc.idxW bh)) (hbd : denoteN st.ns bh = some boolRecName) (hbp : PersN bh)
    (h : NIdx) (n : ConLeche.Name) (hp : PersN h) (hd : denoteN st.ns h = some n)
    (hforb : ∀ j ∈ cellsF, EH[j]? ≠ some (Enc.idxW h)) : n ∉ FN := by
  intro hn
  simp only [FN, List.mem_append, List.mem_singleton] at hn
  rcases hn with (hn | hn) | hn
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
    obtain ⟨hl, hg⟩ := denoteNL_get hdn
    have hi' : i < P.names.size := by simp at hl; omega
    have hg' : denoteN st.ns P.names[i] = some pinNames[i] := by
      have := hg i hi (by simpa using hi'); simpa using this
    have e := ConPanqueque.Pipeline.denoteN_inj hwf hp (hpn _ (Array.getElem_mem hi')) hd hg'
    have h52 : i < 52 := by have := pinNames_length; omega
    exact hforb (64 + i) (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h52, rfl⟩)))
      (by rw [hb.names i hi', e])
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
    obtain ⟨hl, hg⟩ := denoteNL_get hdr
    have hi' : i < P.reserved.length := by omega
    have e := ConPanqueque.Pipeline.denoteN_inj hwf hp (hpr _ (List.getElem_mem hi')) hd (hg i hi hi')
    have h16 : i < 16 := by have := reserved_length; omega
    exact hforb (122 + i) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h16, rfl⟩)))
      (by rw [hb.res i hi', e])
  · subst hn
    have e := ConPanqueque.Pipeline.denoteN_inj hwf hp hbp hd hbd
    exact hforb 138 (by simp [cellsF]) (by rw [hB, e])

/-- The names the environment's guards read are all forbidden. -/
theorem guards_sub : (ConLeche.natOpNames ++ ConLeche.natDivModNames ++ ConLeche.reduceOpNames ++
    [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName, ConLeche.boolTrueName, ConLeche.boolFalseName]).all (fun m => FN.contains m) = true := by
  decide +kernel

theorem nameOK_of_notMem {n : ConLeche.Name} (h : n ∉ FN) : ConPanqueque.Pipeline.NameOK n := by
  have hs := guards_sub
  simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hs
  have nm : ∀ m, (m ∈ ConLeche.natOpNames ∨ m ∈ ConLeche.natDivModNames ∨ m ∈ ConLeche.reduceOpNames ∨ m = ConLeche.natName ∨ m = ConLeche.natZeroName ∨
      m = ConLeche.natSuccName ∨ m = ConLeche.boolTrueName ∨ m = ConLeche.boolFalseName) → m ≠ n := by
    intro m hm e; subst e; apply h
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
    · exact hs m (Or.inl (Or.inl (Or.inl hm)))
    · exact hs m (Or.inl (Or.inl (Or.inr hm)))
    · exact hs m (Or.inl (Or.inr hm))
    · exact hs m (Or.inr (Or.inl hm))
    · exact hs m (Or.inr (Or.inr (Or.inl hm)))
    · exact hs m (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    · exact hs m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
    · exact hs m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))
  refine ⟨?_, fun hm => nm n (Or.inr (Or.inr (Or.inl hm))) rfl, fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) e.symm⟩
  simp only [ConLeche.natOpName, Bool.or_eq_false_iff]
  -- `List.contains` on names
  constructor
  · cases hc : ConLeche.natOpNames.contains n
    · rfl
    · exfalso; exact nm n (Or.inl (by simpa using hc)) rfl
  · cases hc : ConLeche.natDivModNames.contains n
    · rfl
    · exfalso; exact nm n (Or.inr (Or.inl (by simpa using hc))) rfl

theorem denoteDecls_mem {st : EStore} : ∀ {hs : List IDeclaration} {ds : List ConLeche.Declaration},
    denoteDecls st hs = some ds → ∀ d ∈ ds, ∃ dh ∈ hs, denoteDecl st dh = some d
  | [], ds, h, d, hd => by simp [denoteDecls] at h; subst h; cases hd
  | x :: xs, ds, h, d, hd => by
    simp only [denoteDecls] at h
    split at h
    · rename_i a as ha has
      simp only [Option.some.injEq] at h; subst h
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨x, List.mem_cons_self .., ha⟩
      · obtain ⟨dh, hm, e⟩ := denoteDecls_mem has d hd
        exact ⟨dh, List.mem_cons_of_mem _ hm, e⟩
    · cases h

/-- A value record's name, read off its denotation. -/
theorem valName_denote {st : EStore} {dh : IDeclaration} {d : ConLeche.Declaration}
    (hv : ConPanqueque.Bridge.IsChecked st.ns dh) (hni : ∀ b nP, dh ≠ .indDecl b nP) (hp : PersDecl dh)
    (h : denoteDecl st dh = some d) :
    ∃ nh n, recNameW dh = Enc.idxW nh ∧ PersN nh ∧ denoteN st.ns nh = some n ∧
      ConPanqueque.Pipeline.recName d = some n := by
  cases dh with
  | defnDecl cv e hint =>
    simp only [denoteDecl] at h
    split at h
    · rename_i c x hc hx
      simp only [Option.some.injEq] at h; subst h
      simp only [denoteCV] at hc
      split at hc
      · rename_i n lps ty hn hl ht
        simp only [Option.some.injEq] at hc; subst hc
        exact ⟨cv.name, n, rfl, hp.1.name, hn, rfl⟩
      · cases hc
    · cases h
  | thmDecl cv e =>
    simp only [denoteDecl] at h
    split at h
    · rename_i c x hc hx
      simp only [Option.some.injEq] at h; subst h
      simp only [denoteCV] at hc
      split at hc
      · rename_i n lps ty hn hl ht
        simp only [Option.some.injEq] at hc; subst hc
        exact ⟨cv.name, n, rfl, hp.1.name, hn, rfl⟩
      · cases hc
    · cases h
  | opaqueDecl cv e =>
    simp only [denoteDecl] at h
    split at h
    · rename_i c x hc hx
      simp only [Option.some.injEq] at h; subst h
      simp only [denoteCV] at hc
      split at hc
      · rename_i n lps ty hn hl ht
        simp only [Option.some.injEq] at hc; subst hc
        exact ⟨cv.name, n, rfl, hp.1.name, hn, rfl⟩
      · cases hc
    · cases h
  | axiomDecl cv =>
    simp only [denoteDecl] at h
    cases hc : denoteCV st cv with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h; subst h
      have hn := (denoteCV_inv hc).1
      have hs : denoteN st.ns cv.name = some ConLeche.sorryAxName ∨
          denoteN st.ns cv.name = some ConLeche.quotSoundName := hv
      rw [hn] at hs
      have hcs : c.name = ConLeche.sorryAxName ∨ c.name = ConLeche.quotSoundName :=
        hs.imp Option.some.inj Option.some.inj
      exact ⟨cv.name, c.name, rfl, hp.name, hn, by simp [ConPanqueque.Pipeline.recName, hcs]⟩
  | quotDecl k cv =>
    simp only [denoteDecl] at h
    cases hc : denoteCV st cv with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h; subst h
      exact ⟨cv.name, c.name, rfl, hp.name, (denoteCV_inv hc).1, rfl⟩
  | indDecl b nP => exact absurd rfl (hni b nP)

open ConPanqueque.Front ConPanqueque.T.Decl Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
  ConPanqueque.Logic in
/-- **The verdict with the pass**: when the program returns, con-leche parses the input, its pure
checker accepts the declarations, and every declaration is a value record at a name outside `FN`. -/
theorem front_verdict2 {σ : Type} {F rb capD jN cap bufJ : Nat} {b : ByteArray}
    (pins : List INatOpPinSet) (pinsP : List ConLeche.NatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hf : FrontOK C) (fc : FrontCodes σ C) (hc : FoldCodes .verified C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hcF : C.code.lookup fFeed = some (feedPs.map (fun p => (p, ShapeHOL.one)), prologue feedL feedCore, .one))
    (hEB : ∀ j, ecell C j = ecb j)
    (s : AState) (hst : StateOK s) (hoff : s.store.scratchOn = false) (hpo : PinsOK s) (hpp : PersPins s)
    (hpins : PinsDenote s.store pins pinsP) (hA : denoteN s.store.ns default = some .anonymous)
    (hb : PinBlock C.EH s.pins) (bh : NIdx) (hB : C.EH[138]? = some (Enc.idxW bh))
    (hbd : denoteN s.store.ns bh = some boolRecName) (hbp : PersN bh)
    (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ [kZ, kR0, kN0, kR1], x ∈ D) (hDF : ∀ x ∈ forbidVars, x ∈ D)
    (hfl : FrontLay F rb capD jN (jN + cap) (jN + 2 * cap) cap bufJ b) (hcap1 : 1 ≤ cap) (hcapN : cap ≤ ConPanqueque.Scan.natCap)
    (hcap8 : 8 * cap < 2 ^ 64) (hcapD8 : 8 * (rb + 1 + capD) < 2 ^ 64) (hFH : F ≤ C.H.length)
    (hbuf : BufOK C bufJ b)
    (hZb : Γ.get kZb = some (cellA C jN)) (hZn : Γ.get kZn = some (BitVec.ofNat 64 (3 * cap)))
    (hTN : Γ.get fTN = some (cellA C jN)) (hTL : Γ.get fTL = some (cellA C (jN + cap)))
    (hTE : Γ.get fTE = some (cellA C (jN + 2 * cap))) (hC : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hZL : Γ.get kZL = some (Enc.idxW s.pins.zeroLevel))
    (t : PState σ) (ht : Inv C s Γ M D t) :
    Stop (evaluateHOLFiniteState t mainP2).1 ∨
      ((∃ w, (evaluateHOLFiniteState t mainP2).1 = some (.returned (.val (.word w)))) ∧
        ∃ rc, ConLeche.Frontend.parseBytes b = .ok rc ∧
          (∃ F', ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F') pinsP rc.decls.toList
            = .ok (ConLeche.streamEnv rc.decls.toList)) ∧
          ∀ d ∈ rc.decls.toList, ∃ n, ConPanqueque.Pipeline.recName d = some n ∧ n ∉ FN) := by
  have hsz : b.size < USize.size := by
    have := hbuf.small
    simp only [USize.size_eq_two_pow, hbuf.plat.bits]; omega
  have hcells : ∀ j ∈ cellsF, ∃ w, C.EH[j]? = some w := by
    intro j hj
    simp only [cellsF, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hj
    rcases hj with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | rfl
    · exact ⟨_, hb.names i (by rw [hb.size]; simpa [pinCount] using hi)⟩
    · exact ⟨_, hb.res i (by rw [(denoteNL_get hpo.reserved).1, reserved_length]; exact hi)⟩
    · exact ⟨_, hB⟩
  rcases main_spec2 pins ra C hok hf fc hc hs hpl hfe hcF hEB hcells s hst hoff hpo hA Γ M D hD hDF hfl hcap1 hcapN hcap8
      hcapD8 hFH hbuf hZb hZn hTN hTL hTE hC hBA hBN hRB hCD hZL t ht with
    hstop | ⟨w, hw, a, s'', -, st', s', hrun, hval, hm, hforb⟩
  · exact Or.inl hstop
  refine Or.inr ⟨⟨w, hw⟩, ?_⟩
  obtain ⟨hstep, hpersR, rc, hrc, hden⟩ := parse_twin hst hoff hpo hsz hrun
  refine ⟨rc, hrc, ConPanqueque.Bridge.seq_bridge' hstep.ok (hpo.mono hstep.ext hstep.pins) (hpp.mono hstep.pins)
    (PinsDenote.mono hstep.ext _ _ hpins) hden
    (fun pd h => ConPanqueque.Bridge.isChecked_of_front (hpo.mono hstep.ext hstep.pins) (hval pd h)) hm, fun d hd => ?_⟩
  obtain ⟨dh, hdm, hdd⟩ := denoteDecls_mem hden d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdm
  have hk' : k < st'.decls.size := by simpa using hk
  obtain ⟨nh, n, hrw, hpn, hdn, hvn⟩ := valName_denote (ConPanqueque.Bridge.isChecked_of_front (hpo.mono hstep.ext hstep.pins) (hval _ hdm))
    (fun b nP e => by have := hval _ hdm; rw [e] at this; exact this) (hpersR _ (by show st'.decls[k] ∈ st'.decls; exact Array.getElem_mem hk')) hdd
  refine ⟨n, hvn, ?_⟩
  have hpo' := hpo.mono hstep.ext hstep.pins
  have hwf : NStoreWF s'.store.ns := ConRon.Bridge.Frontend.nsWF_of_StateOK hstep.ok
  refine name_notMem s'.store hwf s.pins C.EH hb (by rw [← hstep.pins]; exact hpo'.names)
    (by rw [← hstep.pins]; exact hpo'.reserved) hpp.names hpp.reserved bh hB (denoteN_ext hbd hstep.ext) hbp
    nh n hpn hdn (fun j hj e => hforb k hk' j hj ?_)
  rw [e]; simp only [Array.getElem_toList] at hrw; rw [hrw]

end ConPanqueque.Start
