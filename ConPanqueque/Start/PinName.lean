import ConPanqueque.Start.InitCtx
import ConPanqueque.Front.Name

/-! # Interning a static name

The pin phase interns names known when the program is written.  `strStepP str` interns
`.str p str` for the handle `p` in `vPn`: fresh heap cells for the key, the prefix handle and
the string's bytes stored as constants, then the ported `internNStr`.  `nameP` chains the steps
from the anonymous name (whose handle is the word 0, a hit in the bootstrap store). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front

variable {σ : Type}

def vPn := ofString "ppn"
def vKa := ofString "pka"

theorem inv_env_weaken {C : Ctx} {s : AState} {Γ Γ' : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ M D t) (hg : ∀ x v, Γ'.get x = some v → Γ.get x = some v) : Inv C s Γ' M D t :=
  ⟨h.sr, fun x v hx => h.env x v (hg x v hx), h.mem, h.decl⟩

theorem specR_envWeaken {α : Type} {C : Ctx} {s : AState} {Γ Γ' : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hg : ∀ x v, Γ'.get x = some v → Γ.get x = some v) (h : SpecR (Inv C s Γ' M D) c s m R) :
    SpecR (Inv C s Γ M D) c s m R := fun t ht => h t (inv_env_weaken ht hg)

/-- Store the bytes `bs` as words into the cells from `vKa + 8 i`. -/
def bytesP (i : Nat) : List UInt8 → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | b :: bs, rest => .seq (.store (.op .add [vv vKa, .const (BitVec.ofNat 64 (8 * i))])
      (.const (BitVec.ofNat 64 b.toNat))) (bytesP (i + 1) bs rest)

theorem bytesP_spec {α : Type} (C : Ctx) (hok : CtxOK C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (o : Nat) (hka : Γ.get vKa = some (cellA C o)) :
    ∀ (bs : List UInt8) (i : Nat) (C' : Ctx), C' = ctxH C C'.H → o + i + bs.length ≤ C'.H.length →
    (∀ H' : List (BitVec 64), H'.length = C'.H.length → (∀ j, j < o + i → H'[j]? = C'.H[j]?) →
      (∀ j (hj : j < bs.length), H'[o + i + j]? = some (BitVec.ofNat 64 bs[j].toNat)) →
      SpecR (Inv (ctxH C H') s Γ [] D) rest s m R) →
    SpecR (Inv C' s Γ M D) (bytesP i bs rest) s m R
  | [], i, C', hC, _, hk => by
    simp only [bytesP]
    intro t ht
    refine hk C'.H rfl (fun _ _ => rfl) (fun j hj => absurd hj (by simp)) t ?_
    rw [← hC]; exact ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  | b :: bs, i, C', hC, hroom, hk => by
    simp only [bytesP]
    have hok' : CtxOK C' := by rw [hC]; exact ctxOK_H hok _
    simp only [List.length_cons] at hroom
    refine specR_heapStoreI hok' _ _ (o + i) (by omega) (BitVec.ofNat 64 b.toNat) ?_ rfl ?_
    · simp only [sev, vv, hka, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [hC]; simp only [cellA, ctxH] at *; congr 1
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.mul_add]
    · refine bytesP_spec C hok s Γ [] D o hka bs (i + 1) (ctxH C' (C'.H.set (o + i) _)) (by rw [hC]; rfl)
        (by simp only [ctxH, List.length_set]; omega) (fun H' hl h1 h2 => hk H' (by simpa [ctxH] using hl)
          (fun j hj => by
            rw [h1 j (by omega)]; simp only [ctxH]; rw [List.getElem?_set, ite_eq_right (by omega)])
          (fun j hj => by
            cases j with
            | zero =>
              rw [Nat.add_zero, h1 (o + i) (by omega)]; simp only [ctxH, List.getElem_cons_zero]
              rw [List.getElem?_set_self (by omega)]
            | succ j =>
              simp only [List.getElem_cons_succ]
              rw [show o + i + (j + 1) = o + (i + 1) + j by omega]
              exact h2 j (by simpa using hj)))

theorem prefix_of_agree {A B B' : List (BitVec 64)} (hp : A <+: B) (hl : A.length ≤ B'.length)
    (h : ∀ j, j < A.length → B'[j]? = B[j]?) : A <+: B' := by
  refine ⟨B'.drop A.length, ?_⟩
  apply List.ext_getElem?
  intro j
  by_cases hj : j < A.length
  · rw [List.getElem?_append_left hj, h j hj]
    obtain ⟨r, rfl⟩ := hp
    rw [List.getElem?_append_left hj]
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]; congr 1; omega

def strBytes (str : String) : List UInt8 := str.toByteArray.data.toList

/-- Intern `.str p str`, `p` in `vPn`, the handle back into `vPn`. -/
def strStepP (C : Ctx) (str : String) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C vKa (.const (BitVec.ofNat 64 (8 * ((strBytes str).length + 1))))
    (.seq (.store (vv vKa) (vv vPn))
    (bytesP 1 (strBytes str)
    (.seq (.call (some (some (.local, vPn), none)) fInternNStr
      [vv vKa, .const (BitVec.ofNat 64 ((strBytes str).length + 1)), vv vPn,
        .const (BitVec.ofNat 64 (strBytes str).length)]) rest)))

theorem strStep_spec {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D)
    (p : NIdx) (hp : Γ.get vPn = some (Enc.idxW p)) (str : String) (hn : (strBytes str).length < 2 ^ 50)
    {rest : ProgHOL 64} {k : NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ h s' o, internNNode (.str p str) s = .ok (h, s') →
      SpecR (Inv C s' ((vPn, Enc.idxW h) :: (vKa, cellA C o) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (strStepP C str rest) s (internNNode (.str p str) >>= k) R := by
  have hlay := hok.heapLay
  let n := (strBytes str).length
  unfold strStepP
  refine specR_allocI vKa _ (n + 1) (by omega) hKa (fun v => by simp [sev, n]) (fun H' ws hpre hwl hcapH => ?_)
  have hCH : C.H.length ≤ H'.length := hpre.length_le
  let o := H'.length
  have hl1 : (H' ++ ws).length = o + (n + 1) := by simp [o, hwl]
  refine specR_heapStoreI (C := ctxH C (H' ++ ws)) (ctxOK_H hok _) (vv vKa) (vv vPn) o
    (by simp only [ctxH]; omega) (Enc.idxW p) (by simp [sev, vv, T.Env.get_cons]; rfl)
    (by simp [sev, vv, T.Env.get_cons, show vPn ≠ vKa by decide, hp]) ?_
  let H2 := (H' ++ ws).set o (Enc.idxW p)
  have hl2 : H2.length = o + (n + 1) := by simp [H2, hl1]
  refine bytesP_spec C hok s ((vKa, cellA C o) :: Γ) [] D o (by simp [T.Env.get_cons]) (strBytes str) 1
    (ctxH (ctxH C (H' ++ ws)) H2) rfl (by simp only [ctxH]; omega) (fun H3 hl3 h1 h2 => ?_)
  simp only [ctxH] at hl3 h1
  have hl3' : H3.length = o + (n + 1) := by rw [hl3, hl2]
  have hagree : ∀ j, j < C.H.length → H3[j]? = H'[j]? := by
    intro j hj
    rw [h1 j (by omega)]
    simp only [H2]; rw [List.getElem?_set, ite_eq_right (by omega), List.getElem?_append_left (by omega)]
  have hp3 : C.H <+: H3 := prefix_of_agree hpre (by omega) hagree
  have hkl : (Enc.encStr ⟨p, str⟩).length = n + 1 := by simp [Enc.encStr, Enc.strW, n, strBytes]
  have hkey : ∀ j (hj : j < (Enc.encStr ⟨p, str⟩).length), H3[o + j]? = some ((Enc.encStr ⟨p, str⟩)[j]) := by
    intro j hj
    rw [hkl] at hj
    cases j with
    | zero =>
      rw [Nat.add_zero, h1 o (by omega)]
      simp only [H2, Enc.encStr, List.getElem_cons_zero]
      rw [List.getElem?_set_self (by omega)]
    | succ j =>
      have := h2 j (by omega)
      rw [show o + 1 + j = o + (j + 1) by omega] at this
      rw [this]
      simp [Enc.encStr, Enc.strW, strBytes]
  refine specR_callNIA vPn fInternNStr [pKeyN, lEn, lEp, lHn]
    [vv vKa, .const (BitVec.ofNat 64 (n + 1)), vv vPn, .const (BitVec.ofNat 64 n)] nameStrBody
    [cellA C o, BitVec.ofNat 64 (n + 1), Enc.idxW p, BitVec.ofNat 64 n] (by decide) rfl hPn hcN
    ⟨by simp [sev, vv, T.Env.get_cons], rfl,
     by simp [sev, vv, T.Env.get_cons, show vPn ≠ vKa by decide, hp], rfl, trivial⟩
    (fun a w s' st => internNNode (.str p str) s = .ok (a, s') ∧ PostNm (ctxH (ctxH C H3) C.H) a w s' st)
    (fun a w s' H'' => H'' = C.H ∧ internNNode (.str p str) s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨C.H, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      have hs := nameStr_body_spec (σ := σ) ra (ctxH C H3) (ctxOK_H hok _) (frontOK_H hf _) s p str o C.H hp3
        (by omega) (by rw [hkl]; show o + (n + 1) ≤ H3.length; omega) (by rw [hkl]; omega) hkey
      have e1 : (Enc.encStr ⟨p, str⟩).length = n + 1 := hkl
      have e2 : str.toByteArray.data.toList.length = n := rfl
      rw [e1, e2] at hs
      exact hs _ (pre_of_lookups hu [pKeyN, lEn, lEp, lHn] _ rfl hlk)))
    (fun h w s2 H'' ⟨e, hr2, hw⟩ => ?_)
  subst e; subst hw
  rw [ctxH_ctxH, ctxH_self]
  exact hk h s2 o hr2

/-! ## Whole names -/

/-- A name's string components, root first (`none` for a name with a numeric component). -/
def strComps : ConLeche.Name → Option (List String)
  | .anonymous => some []
  | .str p s => (strComps p).map (· ++ [s])
  | .num _ _ => none

/-- The twin's interns of the components from handle `p`. -/
def internComps (p : NIdx) : List String → AM NIdx
  | [] => pure p
  | c :: cs => internNNode (.str p c) >>= fun h => internComps h cs

theorem internComps_append (p : NIdx) (cs : List String) (c : String) :
    internComps p (cs ++ [c]) = internComps p cs >>= fun h => internNNode (.str h c) := by
  induction cs generalizing p with
  | nil => simp [internComps]
  | cons c' cs ih =>
    simp only [List.cons_append, internComps, ih]
    simp only [bind_assoc]

theorem internName_comps : ∀ (n : ConLeche.Name) (cs : List String), strComps n = some cs →
    internName n = internNNode .anonymous >>= fun a => internComps a cs
  | .anonymous, cs, h => by
    simp only [strComps, Option.some.injEq] at h; subst h
    simp [internName, internComps]
  | .str p c, cs, h => by
    simp only [strComps, Option.map_eq_some_iff] at h
    obtain ⟨cs', h', rfl⟩ := h
    rw [internName, internName_comps p cs' h', bind_assoc]
    congr 1; funext a; rw [internComps_append]
  | .num _ _, cs, h => by simp [strComps] at h

/-- The anonymous name is a hit once it is interned: the handle word 0, the state unchanged. -/
theorem anon_probe {s : AState} (hok : StateOK s) (hd : denoteN s.store.ns default = some .anonymous) :
    internNNode .anonymous s = .ok (default, s) := by
  have hv := view_of_denoteN_anon hd
  obtain ⟨rk, hrk⟩ := ConRon.Bridge.Frontend.nsWF_of_StateOK hok
  have hf := (hrk.consP .anonymous default).mpr ⟨hv, by decide⟩
  simp [internNNode, NStore.find?, hf, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, Except.bind]

def stepsP (C : Ctx) : List String → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | c :: cs, rest => strStepP C c (stepsP C cs rest)

def compsOK (cs : List String) : Prop := ∀ c ∈ cs, (strBytes c).length < 2 ^ 50

theorem steps_spec {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one))
    (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) {rest : ProgHOL 64} {R : β → BitVec 64 → AState → PState σ → Prop} :
    ∀ (cs : List String) (p : NIdx) (s : AState) (Γ : Env) (M : Mem) (k : NIdx → AM β), compsOK cs →
    Γ.get vPn = some (Enc.idxW p) →
    (∀ h s' (Γ' : Env), (∀ y, y ≠ vPn → y ≠ vKa → Γ'.get y = Γ.get y) → Γ'.get vPn = some (Enc.idxW h) →
      internComps p cs s = .ok (h, s') → SpecR (Inv C s' Γ' [] D) rest s' (k h) R) →
    SpecR (Inv C s Γ M D) (stepsP C cs rest) s (internComps p cs >>= k) R
  | [], p, s, Γ, M, k, _, hp, hk => by
    simp only [stepsP, internComps, pure_bind]
    intro t ht
    exact hk p s Γ (fun _ _ _ => rfl) hp rfl t ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  | c :: cs, p, s, Γ, M, k, hcs, hp, hk => by
    simp only [stepsP, internComps, bind_assoc]
    refine strStep_spec ra C hok hf hcN s Γ M D hPn hKa p hp c (hcs c (List.mem_cons_self ..)) (fun h s1 o hr => ?_)
    refine steps_spec ra C hok hf hcN D hPn hKa cs h s1 _ [] k (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
      (by simp [T.Env.get_cons]) (fun h2 s2 Γ' hag hpn hr2 => hk h2 s2 Γ' (fun y h1 h2' => by
        rw [hag y h1 h2']; simp [T.Env.get_cons, h1, h2']) hpn ?_)
    simp only [internComps, bind, StateT.bind, Except.bind, hr]; exact hr2

/-- Intern the static name `n` (string components `cs`) into `vPn`. -/
def nameP (C : Ctx) (cs : List String) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local vPn (.const 0)) (stepsP C cs rest)

theorem idxW_default : Enc.idxW (default : NIdx) = 0 := rfl

theorem name_spec {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one))
    (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) {rest : ProgHOL 64} {R : β → BitVec 64 → AState → PState σ → Prop}
    (n : ConLeche.Name) (cs : List String) (hcs : strComps n = some cs) (hok' : compsOK cs)
    (s : AState) (hst : StateOK s) (hd : denoteN s.store.ns default = some .anonymous) (Γ : Env) (M : Mem)
    (k : NIdx → AM β)
    (hk : ∀ h s' (Γ' : Env), (∀ y, y ≠ vPn → y ≠ vKa → Γ'.get y = Γ.get y) → Γ'.get vPn = some (Enc.idxW h) →
      internName n s = .ok (h, s') → SpecR (Inv C s' Γ' [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (nameP C cs rest) s (internName n >>= k) R := by
  have e : (internName n >>= k) s = (internComps default cs >>= k) s := by
    rw [internName_comps n cs hcs, bind_assoc]
    simp only [bind, StateT.bind, Except.bind, anon_probe hst hd]
  refine specR_congr e ?_
  refine specR_assignI vPn (.const 0) 0 hPn rfl ?_
  refine steps_spec ra C hok hf hcN D hPn hKa cs default s _ M k hok' (by simp [T.Env.get_cons]; rfl)
    (fun h s' Γ' hag hpn hr => hk h s' Γ' (fun y h1 h2 => by rw [hag y h1 h2]; simp [T.Env.get_cons, h1]) hpn ?_)
  rw [internName_comps n cs hcs]
  simp only [bind, StateT.bind, Except.bind, anon_probe hst hd]; exact hr

end ConPanqueque.Start
