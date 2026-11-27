import ConPanqueque.T.Ind.CtorNames

/-!
# The block's constructor names distinct, at any number of members

* `cctBody(om, i, n)`: the constructor count of members `i … n - 1` (a total at or past `2⁵⁸` hangs);
* `cnaBody(om, o, i, n, g)`: the constructor names of members `i …` into the block at `o`, from slot `g`
  (`cnfBody` per member, at the block base `o + g`);
* `mnaBody(om, o, i, n)`: the members' former names from member `i` into the block at `o`;
* `cnkBody(om, n)`: `nameNodup` of all constructor names, and of the member names.

`cnk_spec` refines `nameNodup (allCtors.map name) && nameNodup memberNames`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

/-- The constructors of a list of members, flattened. -/
def flatCtors (ms : List MemberShape) : List (IConstantVal × Nat) := (ms.map (·.ctors)).flatten

/-- The twin's `allCtors` and `memberNames` are what `cnk_spec` checks. -/
theorem flatCtors_allCtors (p : BlockShape) : flatCtors p.members = p.allCtors := rfl

theorem memberNames_eq (p : BlockShape) : p.members.map (·.cvT.name) = p.memberNames := rfl

theorem flatCtors_cons (m : MemberShape) (ms : List MemberShape) : flatCtors (m :: ms) = m.ctors ++ flatCtors ms := rfl

theorem flatCtors_length (ms : List MemberShape) : (flatCtors ms).length = (ms.map (·.ctors.length)).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [flatCtors_cons, ih]

/-! ## The count -/

def cctOm := ofString "cct_om"
def cctI := ofString "cct_i"
def cctN := ofString "cct_n"
def cctMi := ofString "cct_mi"
def cctOl := ofString "cct_ol"
def cctNc := ofString "cct_nc"
def cctR := ofString "cct_r"
def cctS := ofString "cct_s"
def fCct := ofString "ctorCountAll"

def cctParams : List MlS := [cctOm, cctI, cctN]
def cctLocals : List MlS := [cctMi, cctOl, cctNc, cctR, cctS]

def cctBody : ProgHOL 64 := prologue cctLocals
  (.ite (.cmp .lower (vv cctI) (vv cctN))
    (.seq (.assign .local cctMi (.load .one (.op .add [vv cctOm, .op .add [.panop .mul [vv cctI, .const 8], .const 8]])))
    (.seq (.assign .local cctOl (.load .one (.op .add [vv cctMi, .const 24])))
    (.seq (.assign .local cctNc (.load .one (vv cctOl)))
    (.seq (.call (some (some (.local, cctR), none)) fCct [vv cctOm, .op .add [vv cctI, .const 1], vv cctN])
    (.seq (.assign .local cctS (.op .add [vv cctNc, vv cctR]))
    (guardP cctS 58 (.return (vv cctS))))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- A count `n` below `2⁵⁸`, the state kept. -/
def PostCnt (C : Ctx) (s : AState) (n : Nat) (_ : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ n < 2 ^ 58 ∧ w = BitVec.ofNat 64 n ∧ SR C s' st

theorem postCnt_locals (C : Ctx) (s : AState) (n : Nat) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCnt C s n a w s' st → PostCnt C s n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem cct_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cctLocals → (ctxEnv C ++ cctParams.zip vals).get x = none :=
  Knot.params_none C cctLocals cctParams vals (by decide) (by decide)

set_option maxHeartbeats 4000000 in
/-- **The constructor count** of the members from `i` on (at or past `2⁵⁸`: a hang). -/
theorem cct_spec (C : Ctx) (hc : C.code.lookup fCct = some (cctParams.map (fun p => (p, ShapeHOL.one)), cctBody, .one))
    (ms : List MemberShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58)
    (hcl : ∀ m ∈ ms, m.ctors.length < 2 ^ 58) :
    ∀ f i (s : AState), ms.length - i = f → i ≤ ms.length →
      SpecR (σ := σ) (Pre C s (cctParams.zip [cellA C om, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length])) cctBody s
        (pure ()) (PostCnt C s (flatCtors (ms.drop i)).length) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hil : i = ms.length := by omega
    subst hil
    refine specR_prologue (postCnt_locals _ _ _) (cct_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, cctParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, by simp [flatCtors], by simp [flatCtors],
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hil : i < ms.length := by omega
    refine specR_prologue (postCnt_locals _ _ _) (cct_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, cctParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨mi, hmi, hrep⟩ := hM.2 i hil
    obtain ⟨-, -, -, ⟨ol, hol, hctr⟩⟩ := hrep
    refine UD.specR_heapLoadI' (C := C) cctMi _ (om + 1 + i) _ hmi (by decide)
      (by simp +decide [sev, Env.get, cctParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := C) cctOl _ (mi + 3) _ hol (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C mi 3) ?_
    refine UD.specR_heapLoadI' (C := C) cctNc (vv cctOl) ol _ hctr.1 (by decide) (by simp [sev, Env.get_cons]) ?_
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIM cctR fCct cctParams [vv cctOm, .op .add [vv cctI, .const 1], vv cctN] cctBody
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cctParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cctParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cctParams, ctxEnv], trivial⟩
      (PostCnt C s (flatCtors (ms.drop (i + 1))).length) (fun _ _ _ _ h => h.2.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cctParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun _ w s1 st ⟨hs1, hlt, hw, _⟩ => ?_)
    subst s1 hw
    have hci : ms[i].ctors.length < 2 ^ 58 := hcl _ (List.getElem_mem hil)
    have hlen : (flatCtors (ms.drop i)).length = ms[i].ctors.length + (flatCtors (ms.drop (i + 1))).length := by
      rw [List.drop_eq_getElem_cons hil, flatCtors_cons, List.length_append]
    refine specR_assignI cctS _ (BitVec.ofNat 64 (flatCtors (ms.drop i)).length) (by decide)
      (by simp +decide [sev, Env.get_cons]; rw [BitVec.ofNat_add_ofNat, hlen]) ?_
    refine specR_guardI cctS (flatCtors (ms.drop i)).length 58 (by decide) (by simp [Env.get_cons]) (by omega)
      (fun h58 => ?_)
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, h58, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The constructor names of the members, into one block -/

def cnaOm := ofString "cna_om"
def cnaO := ofString "cna_o"
def cnaI := ofString "cna_i"
def cnaN := ofString "cna_n"
def cnaG := ofString "cna_g"
def cnaMi := ofString "cna_mi"
def cnaOl := ofString "cna_ol"
def cnaNc := ofString "cna_nc"
def cnaX := ofString "cna_x"
def cnaY := ofString "cna_y"
def fCna := ofString "ctorNamesFillAll"

def cnaParams : List MlS := [cnaOm, cnaO, cnaI, cnaN, cnaG]
def cnaLocals : List MlS := [cnaMi, cnaOl, cnaNc, cnaX, cnaY]

def cnaBody : ProgHOL 64 := prologue cnaLocals
  (.ite (.cmp .lower (vv cnaI) (vv cnaN))
    (.seq (.assign .local cnaMi (.load .one (.op .add [vv cnaOm, .op .add [.panop .mul [vv cnaI, .const 8], .const 8]])))
    (.seq (.assign .local cnaOl (.load .one (.op .add [vv cnaMi, .const 24])))
    (.seq (.assign .local cnaNc (.load .one (vv cnaOl)))
    (.seq (.call (some (some (.local, cnaX), none)) fCnFillN
        [vv cnaOl, .op .add [vv cnaO, .panop .mul [vv cnaG, .const 8]], .const 0, vv cnaNc])
    (.seq (.call (some (some (.local, cnaY), none)) fCna
        [vv cnaOm, vv cnaO, .op .add [vv cnaI, .const 1], vv cnaN, .op .add [vv cnaG, vv cnaNc]])
      (.return (.const 0)))))))
    (.return (.const 0)))

theorem cellA_mul8' (C : Ctx) (o i : Nat) (hi : i < 2 ^ 61) :
    cellA C o + BitVec.ofNat 64 i * 8#64 = cellA C (o + i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

section
variable {σ : Type}

/-- The names `L` written from slot `g` of the block at `o`, past the frozen prefix `Hc`. -/
def PostCNA (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (L : List (IConstantVal × Nat)) (g : Nat) (_ : Unit)
    (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ ∀ j (hj : j < L.length), H'[o + 1 + g + j]? = some (Enc.idxW L[j].1.name)

theorem postCNA_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (L : List (IConstantVal × Nat)) (g : Nat) :
    ∀ a w s' (st : PState σ) (L' : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCNA C Hc o L g a w s' st → PostCNA C Hc o L g a w s' { st with locals := L' } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem cna_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnaLocals → (ctxEnv C ++ cnaParams.zip vals).get x = none :=
  Knot.params_none C cnaLocals cnaParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **The constructor names of the members from `i` on**, from slot `g` of the block at `o`. -/
theorem cna_spec (C : Ctx) (hok : CtxOK C)
    (hfill : C.code.lookup fCnFillN = some (cnfParams.map (fun p => (p, ShapeHOL.one)), cnfBody, .one))
    (hc : C.code.lookup fCna = some (cnaParams.map (fun p => (p, ShapeHOL.one)), cnaBody, .one))
    (ms : List MemberShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58)
    (hcl : ∀ m ∈ ms, m.ctors.length < 2 ^ 58) (o : Nat) :
    ∀ f i g (H Hc : List (BitVec 64)) (s : AState), ms.length - i = f → i ≤ ms.length → C.H <+: Hc →
      Hc.length ≤ o + 1 + g → Hc <+: H → o + 1 + g + (flatCtors (ms.drop i)).length ≤ H.length →
      g + (flatCtors (ms.drop i)).length < 2 ^ 58 →
      SpecR (σ := σ) (Pre (ctxH C H) s (cnaParams.zip [cellA C om, cellA C o, BitVec.ofNat 64 i,
        BitVec.ofNat 64 ms.length, BitVec.ofNat 64 g])) cnaBody s (pure ()) (PostCNA C Hc o (flatCtors (ms.drop i)) g) := by
  intro f
  induction f with
  | zero =>
    intro i g H Hc s hf hi h0 hHc hp hl hg
    have hil : i = ms.length := by omega
    subst hil
    refine specR_prologue (postCNA_locals _ _ _ _ _) (cna_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, cnaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => by
      simp [flatCtors] at hj⟩)
  | succ f ih =>
    intro i g H Hc s hf hi h0 hHc hp hl hg
    have hil : i < ms.length := by omega
    refine specR_prologue (postCNA_locals _ _ _ _ _) (cna_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, cnaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨mi, hmi, hrep⟩ := hM.2 i hil
    obtain ⟨-, -, -, ⟨ol, hol, hctr⟩⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) cnaMi _ (om + 1 + i) _ (ConPanqueque.T.Decl.get_prefix hmi h0H) (by decide)
      (by simp +decide [sev, Env.get, cnaParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnaOl _ (mi + 3) _ (ConPanqueque.T.Decl.get_prefix hol h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C mi 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cnaNc (vv cnaOl) ol _ (ConPanqueque.T.Decl.get_prefix hctr.1 h0H)
      (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    set cs := ms[i].ctors with hcs
    set L' := flatCtors (ms.drop (i + 1)) with hL'
    have hLi : flatCtors (ms.drop i) = cs ++ L' := by rw [List.drop_eq_getElem_cons hil, flatCtors_cons]
    have hci : cs.length < 2 ^ 58 := hcl _ (List.getElem_mem hil)
    have hll : (flatCtors (ms.drop i)).length = cs.length + L'.length := by rw [hLi, List.length_append]
    refine specR_pureBind () ?_
    refine specR_callNIG (C := ctxH C H) cnaX fCnFillN cnfParams
      [vv cnaOl, .op .add [vv cnaO, .panop .mul [vv cnaG, .const 8]], .const 0, vv cnaNc] cnfBody
      [cellA C ol, cellA C (o + g), BitVec.ofNat 64 0, BitVec.ofNat 64 cs.length] (by decide) rfl (by decide) hfill
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cnaParams, ctxEnv]; exact cellA_mul8' C o g (by omega), rfl,
        by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCNF C Hc (o + g) cs 0 H.length a w s' st)
      (fun a w s' H' => s' = s ∧ Hc <+: H' ∧ H.length ≤ H'.length ∧
        ∀ j (hj : j < cs.length), 0 ≤ j → H'[o + g + 1 + j]? = some (Enc.idxW cs[j].1.name))
      (fun a w s' st ⟨hr, H', hp', hl', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact cnf_spec C hok hfill cs ol (o + g) C.H hctr hci _ 0 H Hc s rfl (Nat.zero_le _)
          h0 (by omega) hp (by omega) _ (pre_of_lookups hu cnfParams _ rfl hlk)))
      (fun a w s1 H1 ⟨hs1, hp1, hl1, hc1⟩ => ?_)
    subst s1
    let Hc' := H1.take (o + 1 + g + cs.length)
    have hpc' : Hc' <+: H1 := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp1.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hp1
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIG (C := ctxH C H1) cnaY fCna cnaParams
      [vv cnaOm, vv cnaO, .op .add [vv cnaI, .const 1], vv cnaN, .op .add [vv cnaG, vv cnaNc]] cnaBody
      [cellA C om, cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length, BitVec.ofNat 64 (g + cs.length)]
      (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cnaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnaParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cnaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cnaParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCNA C Hc' o L' (g + cs.length) a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧
        ∀ j (hj : j < L'.length), H'[o + 1 + (g + cs.length) + j]? = some (Enc.idxW L'[j].1.name))
      (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) (g + cs.length) H1 Hc' s (by omega) (by omega) (h0.trans hHcc)
          (by simp [Hc']; omega) hpc' (by rw [← hL']; omega) (by rw [← hL']; omega) _
          (pre_of_lookups hu cnaParams _ rfl hlk)))
      (fun a w s2 H2 ⟨hs2, hp2, hc2⟩ => ?_)
    subst hs2
    refine specR_returnI _ 0 rfl (fun t ht => ⟨H2, hHcc.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => ?_⟩)
    rw [hll] at hj
    have hgj : (flatCtors (ms.drop i))[j]'(by omega) = (cs ++ L')[j]'(by simp; omega) := by simp only [hLi]
    rw [hgj]
    rcases Nat.lt_or_ge j cs.length with h | h
    · rw [List.getElem_append_left h]
      have hx : Hc'[o + 1 + g + j]? = some (Enc.idxW cs[j].1.name) := by
        simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), show o + 1 + g + j = o + g + 1 + j by omega]
        exact hc1 j h (Nat.zero_le _)
      exact ConPanqueque.T.Decl.get_prefix hx hp2
    · rw [List.getElem_append_right h]
      have := hc2 (j - cs.length) (by omega)
      rw [show o + 1 + (g + cs.length) + (j - cs.length) = o + 1 + g + j by omega] at this
      exact this

end

/-! ## The member names, into one block -/

def mnaOm := ofString "mna_om"
def mnaO := ofString "mna_o"
def mnaI := ofString "mna_i"
def mnaN := ofString "mna_n"
def mnaMi := ofString "mna_mi"
def mnaOc := ofString "mna_oc"
def mnaY := ofString "mna_y"
def mnaR := ofString "mna_r"
def fMna := ofString "memberNamesFillAll"

def mnaParams : List MlS := [mnaOm, mnaO, mnaI, mnaN]
def mnaLocals : List MlS := [mnaMi, mnaOc, mnaY, mnaR]

def mnaBody : ProgHOL 64 := prologue mnaLocals
  (.ite (.cmp .lower (vv mnaI) (vv mnaN))
    (.seq (.assign .local mnaMi (.load .one (.op .add [vv mnaOm, .op .add [.panop .mul [vv mnaI, .const 8], .const 8]])))
    (.seq (.assign .local mnaOc (.load .one (vv mnaMi)))
    (.seq (.assign .local mnaY (.load .one (vv mnaOc)))
    (.seq (.store (.op .add [vv mnaO, .op .add [.panop .mul [vv mnaI, .const 8], .const 8]]) (vv mnaY))
    (.seq (.call (some (some (.local, mnaR), none)) fMna [vv mnaOm, vv mnaO, .op .add [vv mnaI, .const 1], vv mnaN])
      (.return (.const 0)))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- The member names from position `i` on, past the frozen prefix `Hc`, the image at least `n` long. -/
def PostMNA (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (ms : List MemberShape) (i n : Nat) (_ : Unit)
    (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ n ≤ H'.length ∧ SR (ctxH C H') s' st ∧
    ∀ j (hj : j < ms.length), i ≤ j → H'[o + 1 + j]? = some (Enc.idxW ms[j].cvT.name)

theorem postMNA_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (ms : List MemberShape) (i n : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostMNA C Hc o ms i n a w s' st → PostMNA C Hc o ms i n a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hl, hs, h⟩ => ⟨H', hp, hl, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem mna_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mnaLocals → (ctxEnv C ++ mnaParams.zip vals).get x = none :=
  Knot.params_none C mnaLocals mnaParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **The member-names fill** from position `i`. -/
theorem mna_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fMna = some (mnaParams.map (fun p => (p, ShapeHOL.one)), mnaBody, .one))
    (ms : List MemberShape) (om o : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → C.H <+: Hc →
      Hc.length ≤ o + 1 + i → Hc <+: H → o + 1 + ms.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (mnaParams.zip [cellA C om, cellA C o, BitVec.ofNat 64 i,
        BitVec.ofNat 64 ms.length])) mnaBody s (pure ()) (PostMNA C Hc o ms i H.length) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi h0 hHc hp hl
    refine specR_prologue (postMNA_locals _ _ _ _ _ _) (mna_none _ _) ?_
    have hil : i = ms.length := by omega
    subst hil
    have hlw := ConPanqueque.T.Decl.nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, mnaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, le_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc s hk hi h0 hHc hp hl
    have hil : i < ms.length := by omega
    refine specR_prologue (postMNA_locals _ _ _ _ _ _) (mna_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by
        simp +decide [sev, Env.get, mnaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨mi, hmi, hrep⟩ := hM.2 i hil
    obtain ⟨⟨oc, hoc, hcv⟩, -, -, -⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) mnaMi _ (om + 1 + i) _ (ConPanqueque.T.Decl.get_prefix hmi h0H)
      (by decide) (by simp +decide [sev, Env.get, mnaParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mnaOc (vv mnaMi) mi _ (ConPanqueque.T.Decl.get_prefix hoc h0H)
      (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mnaY (vv mnaOc) oc _ (ConPanqueque.T.Decl.get_prefix hcv.1 h0H)
      (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hj : o + 1 + i < (ctxH C H).H.length := by show o + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv mnaY) (o + 1 + i) hj (Enc.idxW ms[i].cvT.name)
      (by simp +decide [sev, Env.get_cons, Env.get, mnaParams, ctxEnv]; exact cellA_mulIdx C o i (by omega))
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (o + 1 + i) (Enc.idxW ms[i].cvT.name))) _ _ _ _) _ _ _ _
    generalize hB : H.set (o + 1 + i) (Enc.idxW ms[i].cvT.name) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[o + 1 + i]? = some (Enc.idxW ms[i].cvT.name) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hp
    let Hc' := B.take (o + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIG (C := ctxH C B) mnaR fMna mnaParams [vv mnaOm, vv mnaO, .op .add [vv mnaI, .const 1], vv mnaN]
      mnaBody [cellA C om, cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide)
      hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mnaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mnaParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mnaParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, mnaParams, ctxEnv], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostMNA C Hc' o ms (i + 1) B.length a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧ H.length ≤ H'.length ∧
        ∀ j (hj : j < ms.length), i + 1 ≤ j → H'[o + 1 + j]? = some (Enc.idxW ms[j].cvT.name))
      (fun a w s' st ⟨hr, H', hp', hl', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hBl ▸ hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega) _
          (pre_of_lookups hu mnaParams _ rfl hlk)))
      (fun a w s' H' ⟨hs', hp', hl', hc'⟩ => ?_)
    subst hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', hl', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
      rcases Nat.lt_or_ge i j with h | h
      · exact hc' j hj (by omega)
      · have e : j = i := by omega
        subst e
        exact ConPanqueque.T.Decl.get_prefix (show Hc'[o + 1 + j]? = some (Enc.idxW ms[j].cvT.name) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'⟩)

end

/-! ## The names' check -/

def cnkOm := ofString "cnk_om"
def cnkN := ofString "cnk_n"
def cnkCnt := ofString "cnk_cnt"
def cnkNb := ofString "cnk_nb"
def cnkX := ofString "cnk_x"
def cnkR1 := ofString "cnk_r1"
def cnkMb := ofString "cnk_mb"
def cnkY := ofString "cnk_y"
def cnkR2 := ofString "cnk_r2"
def fCnk := ofString "blockNamesNodup"

def cnkParams : List MlS := [cnkOm, cnkN]
def cnkLocals : List MlS := [cnkCnt, cnkNb, cnkX, cnkR1, cnkMb, cnkY, cnkR2]

/-- `nameNodup` of all constructor names (the members at `cnkOm`, `cnkN` of them), then of the member names. -/
def cnkBody (C : Ctx) : ProgHOL 64 := prologue cnkLocals
  (.seq (.call (some (some (.local, cnkCnt), none)) fCct [vv cnkOm, .const 0, vv cnkN])
  (allocP C cnkNb (.shift .lsl (.op .add [vv cnkCnt, .const 1]) (.const 3))
  (.seq (.store (vv cnkNb) (vv cnkCnt))
  (.seq (.call (some (some (.local, cnkX), none)) fCna [vv cnkOm, vv cnkNb, .const 0, vv cnkN, .const 0])
  (.seq (.call (some (some (.local, cnkR1), none)) fNdg [vv cnkNb, .const 0, vv cnkCnt])
  (.ite (.cmp .equal (vv cnkR1) (.const 0)) (.return (.const 0))
  (allocP C cnkMb (.shift .lsl (.op .add [vv cnkN, .const 1]) (.const 3))
  (.seq (.store (vv cnkMb) (vv cnkN))
  (.seq (.call (some (some (.local, cnkY), none)) fMna [vv cnkOm, vv cnkMb, .const 0, vv cnkN])
  (.seq (.call (some (some (.local, cnkR2), none)) fNdg [vv cnkMb, .const 0, vv cnkN])
    (.return (vv cnkR2))))))))))))

structure CNKCodes (C : Ctx) : Prop where
  fill : C.code.lookup fCnFillN = some (cnfParams.map (fun p => (p, ShapeHOL.one)), cnfBody, .one)
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  cct : C.code.lookup fCct = some (cctParams.map (fun p => (p, ShapeHOL.one)), cctBody, .one)
  cna : C.code.lookup fCna = some (cnaParams.map (fun p => (p, ShapeHOL.one)), cnaBody, .one)
  mna : C.code.lookup fMna = some (mnaParams.map (fun p => (p, ShapeHOL.one)), mnaBody, .one)
  self : C.code.lookup fCnk = some (cnkParams.map (fun p => (p, ShapeHOL.one)), cnkBody C, .one)

section
variable {σ : Type}

theorem cnk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cnkLocals → (ctxEnv C ++ cnkParams.zip vals).get x = none :=
  Knot.params_none C cnkLocals cnkParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **The block's names distinct**: `nameNodup` of every member's constructor names, and of the member names. -/
theorem cnk_spec (C : Ctx) (hok : CtxOK C) (hc : CNKCodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 58) (hcl : ∀ m ∈ ms, m.ctors.length < 2 ^ 58)
    (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cnkParams.zip [cellA C om, BitVec.ofNat 64 ms.length])) (cnkBody C) s
      (pure (nameNodup ((flatCtors ms).map (·.1.name)) && nameNodup (ms.map (·.cvT.name)))) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (cnk_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hMH : PtrsRep (ctxH C H) (ctxH C H).H om (MemberRep (ctxH C H) (ctxH C H).H) ms :=
    ptrsRep_mono hp (fun _ _ => memberRep_mono hp) hM
  -- the count
  refine specR_pureBind () ?_
  refine specR_callNIM (C := ctxH C H) cnkCnt fCct cctParams [vv cnkOm, .const 0, vv cnkN] cctBody
    [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc.cct
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], trivial⟩
    (PostCnt (ctxH C H) s (flatCtors (ms.drop 0)).length) (fun _ _ _ _ h => h.2.2.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cctParams _ rfl hlk)
      (cct_spec (ctxH C H) hc.cct ms om hMH hml hcl _ 0 s rfl (Nat.zero_le _)))
    (fun _ w s1 st ⟨hs1, hlt, hw, _⟩ => ?_)
  subst s1 hw
  rw [List.drop_zero] at hlt ⊢
  set L := flatCtors ms with hL
  -- the names' block
  refine specR_allocI (C := ctxH C H) cnkNb _ (L.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get_cons]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H <+: H2 := hp2
  have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv cnkNb) (vv cnkCnt) H2.length hq0 (BitVec.ofNat 64 L.length)
    (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 L.length))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 L.length) = B
  have hBlen : B.length = H2.length + (L.length + 1) := by rw [← hB]; simp [hws]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B) cnkX fCna cnaParams [vv cnkOm, vv cnkNb, .const 0, vv cnkN, .const 0] cnaBody
    [cellA C om, cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length, BitVec.ofNat 64 0] (by decide) rfl
    (by decide) hc.cna
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], rfl, trivial⟩
    (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostCNA C Hc H2.length (flatCtors (ms.drop 0)) 0 a w s' st)
    (fun a w s' H' => s' = s ∧ Hc <+: H' ∧
      ∀ j (hj : j < L.length), H'[H2.length + 1 + 0 + j]? = some (Enc.idxW L[j].1.name))
    (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨H', ⟨rfl, hp', by simpa using hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact cna_spec C hok hc.fill hc.cna ms om hM hml hcl H2.length _ 0 0 B Hc s rfl (Nat.zero_le _)
        (hp.trans (hp2'.trans hpc)) (by simp [Hc]) (List.take_prefix _ _) (by rw [List.drop_zero, ← hL]; omega)
        (by rw [List.drop_zero, ← hL]; omega) _
        (pre_of_lookups hu cnaParams _ rfl hlk)))
    (fun a w s' H3 ⟨hs', hp3, hc3⟩ => ?_)
  subst s'
  have hp3' : H <+: H3 := hp2'.trans (hpc.trans hp3)
  have hns : BlkAt H3 H2.length ((L.map (·.1.name)).map Enc.idxW) := by
    refine ⟨?_, fun j hj => ?_⟩
    · have h0 : B[H2.length]? = some (BitVec.ofNat 64 L.length) := by
        rw [← hB, List.getElem?_set_self (by simp; omega)]
      have h0' : Hc[H2.length]? = some (BitVec.ofNat 64 L.length) := by
        simp only [Hc]; rw [List.getElem?_take_of_lt (by omega)]; exact h0
      simpa using ConPanqueque.T.Decl.get_prefix h0' hp3
    · simp only [List.length_map] at hj
      simp only [List.map_map, List.getElem_map, Function.comp]
      simpa using hc3 j hj
  refine specR_congr (m' := (pure (nameNodup ((L.map (·.1.name)).drop 0)) : AM Bool) >>= fun b1 =>
      pure (b1 && nameNodup (ms.map (·.cvT.name)))) (by simp) ?_
  refine specR_callNIH (C := ctxH C H3) cnkR1 fNdg ndgParams [vv cnkNb, .const 0, vv cnkCnt] ndgBody
    [cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 (L.map (·.1.name)).length] (by decide) rfl (by decide) hc.ndg
    ⟨by simp +decide [sev, Env.get_cons]; rfl, rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostB (ctxH C H3)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
      (ndg_spec C hc.ndh hc.ndg (L.map (fun x => x.1.name)) H2.length (by simp; omega) _ 0 H3 s
        (hp.trans hp3') hns rfl (Nat.zero_le _)))
    (fun b1 w s4 H4 hp4 hw => ?_)
  subst hw
  have hp4' : H3 <+: H4 := hp4
  cases hb1 : b1
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hp3'.trans hp4', by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.true_and]
  -- the member names' block
  refine specR_allocI (C := ctxH C H4) cnkMb _ (ms.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H5 ws5 hp5 hws5 hroom5 => ?_)
  · simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp5' : H4 <+: H5 := hp5
  have hq5 : H5.length < (ctxH (ctxH C H4) (H5 ++ ws5)).H.length := by show H5.length < (H5 ++ ws5).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv cnkMb) (vv cnkN) H5.length hq5 (BitVec.ofNat 64 ms.length)
    (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv]) ?_
  change SpecR (Inv (ctxH C ((H5 ++ ws5).set H5.length (BitVec.ofNat 64 ms.length))) _ _ _ _) _ _ _ _
  generalize hB5 : (H5 ++ ws5).set H5.length (BitVec.ofNat 64 ms.length) = B5
  have hB5len : B5.length = H5.length + (ms.length + 1) := by rw [← hB5]; simp [hws5]
  have hpB5 : H5 <+: B5 := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB5, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc5 := B5.take (H5.length + 1)
  have hpc5 : H5 <+: Hc5 := by
    refine prefix_of_get? (by simp [Hc5]; omega) (fun j hj => ?_)
    simp only [Hc5]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB5
  have hpC5 : C.H <+: Hc5 := hp.trans (hp3'.trans (hp4'.trans (hp5'.trans hpc5)))
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B5) cnkY fMna mnaParams [vv cnkOm, vv cnkMb, .const 0, vv cnkN] mnaBody
    [cellA C om, cellA C H5.length, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc.mna
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], by simp +decide [sev, Env.get_cons]; rfl, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧ PostMNA C Hc5 H5.length ms 0 B5.length a w s' st)
    (fun a w s' H' => s' = s4 ∧ Hc5 <+: H' ∧
      ∀ j (hj : j < ms.length), H'[H5.length + 1 + j]? = some (Enc.idxW ms[j].cvT.name))
    (fun a w s' st ⟨hr, H', hp', _, hs', hc'⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨H', ⟨rfl, hp', fun j hj => hc' j hj (Nat.zero_le _)⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact mna_spec C hok hc.mna ms om H5.length hM hml _ 0 B5 Hc5 s4 rfl (Nat.zero_le _) hpC5 (by simp [Hc5])
        (List.take_prefix _ _) (by omega) _ (pre_of_lookups hu mnaParams _ rfl hlk)))
    (fun a w s' H6 ⟨hs', hp6, hc6⟩ => ?_)
  subst s'
  have hp6' : H4 <+: H6 := hp5'.trans (hpc5.trans hp6)
  have hmn : BlkAt H6 H5.length ((ms.map (·.cvT.name)).map Enc.idxW) := by
    refine ⟨?_, fun j hj => ?_⟩
    · have h0 : B5[H5.length]? = some (BitVec.ofNat 64 ms.length) := by
        rw [← hB5, List.getElem?_set_self (by simp; omega)]
      have h0' : Hc5[H5.length]? = some (BitVec.ofNat 64 ms.length) := by
        simp only [Hc5]; rw [List.getElem?_take_of_lt (by omega)]; exact h0
      simpa using ConPanqueque.T.Decl.get_prefix h0' hp6
    · simp only [List.length_map] at hj
      simp only [List.map_map, List.getElem_map, Function.comp]
      exact hc6 j hj
  refine specR_congr (m' := (pure (nameNodup ((ms.map (·.cvT.name)).drop 0)) : AM Bool) >>= fun r => pure r)
    (by rw [List.drop_zero, bind_pure]) ?_
  refine specR_callNIH (C := ctxH C H6) cnkR2 fNdg ndgParams [vv cnkMb, .const 0, vv cnkN] ndgBody
    [cellA C H5.length, BitVec.ofNat 64 0, BitVec.ofNat 64 (ms.map (·.cvT.name)).length] (by decide) rfl (by decide)
    hc.ndg
    ⟨by simp +decide [sev, Env.get_cons]; rfl, rfl,
      by simp +decide [sev, Env.get_cons, Env.get, cnkParams, ctxEnv], trivial⟩
    (PostB (ctxH C H6)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
      (ndg_spec C hc.ndh hc.ndg (ms.map (fun x => x.cvT.name)) H5.length (by simp; omega) _ 0 H6 s4
        (hp.trans (hp3'.trans (hp4'.trans hp6'))) hmn rfl (Nat.zero_le _)))
    (fun r w s7 H7 hp7 hw => ?_)
  subst hw
  have hp7' : H6 <+: H7 := hp7
  exact specR_returnI _ _ (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H7, hp3'.trans (hp4'.trans (hp6'.trans hp7')), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
