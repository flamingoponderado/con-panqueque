import ConPanqueque.Start.PinName
import ConPanqueque.T.Decl.EnvGrow
import ConPanqueque.T.Env

/-! # The pin phase's name lists

The pin phase runs in the bootstrap family `Cb code H EH` (the bootstrap context with its value
heap and environment heap grown).  `namesP` interns a list of static names, storing each handle
into the environment block at `vPb` (cells `b + i, b + i + 1, …`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Code ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Start

open ConPanqueque.Front

variable {σ : Type}

set_option maxRecDepth 100000

def vPb := ofString "ppb"

/-- The bootstrap family. -/
def Cb (code : Code) (H EH : List (BitVec 64)) : Ctx := ctxOf code H none bootStore (feStart P0) EH ∅ ∅ P0 PO0

theorem C0_eq (code : Code) : C0 code = Cb code Himg EH0 := rfl

theorem ctxE_Cb (code : Code) (H EH EH' : List (BitVec 64)) : ctxE (Cb code H EH) EH' = Cb code H EH' := rfl
theorem ctxH_Cb (code : Code) (H EH H' : List (BitVec 64)) : ctxH (Cb code H EH) H' = Cb code H' EH := rfl

theorem Cb_EH (code : Code) (H EH : List (BitVec 64)) : (Cb code H EH).EH = EH := rfl
theorem Cb_H (code : Code) (H EH : List (BitVec 64)) : (Cb code H EH).H = H := rfl
theorem Cb_HB (code : Code) (H EH H' EH' : List (BitVec 64)) : (Cb code H EH).HB = (Cb code H' EH').HB := rfl
theorem Cb_HN (code : Code) (H EH H' EH' : List (BitVec 64)) : (Cb code H EH).HN = (Cb code H' EH').HN := rfl
theorem Cb_code (code : Code) (H EH : List (BitVec 64)) : (Cb code H EH).code = code := rfl

theorem envRel_Cb (code : Code) (H EH : List (BitVec 64)) : EnvRel (Cb code H EH) :=
  ⟨fun n => by simp only [Cb, ctxOf, feStart_find]; simp,
   fun n => by simp only [Cb, ctxOf, feStart_findTable]; simp⟩

theorem pinsE_Cb (code : Code) (H EH : List (BitVec 64)) (hEH : ∀ j, j < 64 → EH[j]? = EH0[j]?) :
    PinsE (Cb code H EH) := by
  refine ⟨by simp [Cb, ctxOf, P0, pinCount], fun i hi => ?_, ?_, ?_, ?_, ⟨?_, by simp [Cb, ctxOf, maxNatSizeDefault,
    P0, Pins.empty]⟩, ⟨w64 (base + E0 + 8 * 57), ?_, 57, ?_, ?_, fun i hi => absurd hi (by simp [Cb, ctxOf, P0, Pins.empty])⟩⟩
  · have hi' : i < 52 := by simpa [Cb, ctxOf, P0, pinCount] using hi
    simp only [Cb, ctxOf, P0, PO0, Nat.zero_add, Array.getElem_replicate]
    rw [hEH _ (by omega)]
    simp [EH0, show i < 64 by omega, show i ≠ 55 by omega, show i ≠ 56 by omega]; rfl
  · simp only [Cb, ctxOf, PO0]; rw [hEH _ (by simp [pinCount])]; simp [EH0, pinCount, P0, Pins.empty]; rfl
  · simp only [Cb, ctxOf, PO0]; rw [hEH _ (by simp [pinCount])]; simp [EH0, pinCount, P0, Pins.empty]; rfl
  · simp only [Cb, ctxOf, PO0]; rw [hEH _ (by simp [pinCount])]; simp [EH0, pinCount, P0, Pins.empty]; rfl
  · simp only [Cb, ctxOf, PO0]; rw [hEH _ (by simp [pinCount])]
    simp [EH0, pinCount, w64, maxNatSizeDefault, P0, Pins.empty]
  · simp only [Cb, ctxOf, PO0]; rw [hEH _ (by simp [pinCount])]; simp [EH0, pinCount]
  · simp [Cb, ctxOf, w64, addr_add]
  · simp only [Cb, ctxOf, P0, Pins.empty, List.map_nil, List.length_nil]
    rw [hEH _ (by omega)]; simp [EH0]

theorem ctxOK_Cb (code : Code) (H EH : List (BitVec 64)) (hEH : ∀ j, j < 64 → EH[j]? = EH0[j]?) :
    CtxOK (Cb code H EH) :=
  ctxOK_ctxOf _ _ _ _ _ _ _ _ _ _ (envRel_Cb code H EH) (pinsE_Cb code H EH hEH)

theorem frontOK_Cb (code : Code) (H EH : List (BitVec 64)) : FrontOK (Cb code H EH) := frontOK_ctxOf _ _ _ _ _ _ _ _ _ _

/-! ## Programs depend on the context only through its heap bounds -/

theorem allocP_congr {C C' : Ctx} (h1 : C.HB = C'.HB) (h2 : C.HN = C'.HN) (x : MlS) (e : ExpHOL 64) (r : ProgHOL 64) :
    allocP C x e r = allocP C' x e r := by unfold allocP; rw [h1, h2]

theorem strStepP_congr {C C' : Ctx} (h1 : C.HB = C'.HB) (h2 : C.HN = C'.HN) (str : String) (r : ProgHOL 64) :
    strStepP C str r = strStepP C' str r := by unfold strStepP; rw [allocP_congr h1 h2]

theorem stepsP_congr {C C' : Ctx} (h1 : C.HB = C'.HB) (h2 : C.HN = C'.HN) :
    ∀ (cs : List String) (r : ProgHOL 64), stepsP C cs r = stepsP C' cs r
  | [], _ => rfl
  | c :: cs, r => by simp only [stepsP]; rw [stepsP_congr h1 h2 cs r, strStepP_congr h1 h2]

theorem nameP_congr {C C' : Ctx} (h1 : C.HB = C'.HB) (h2 : C.HN = C'.HN) (cs : List String) (r : ProgHOL 64) :
    nameP C cs r = nameP C' cs r := by unfold nameP; rw [stepsP_congr h1 h2]

/-- Intern the names (string components `css`), each handle into cell `b + i` of the block at `vPb`. -/
def namesP (C : Ctx) (bv : MlS) : List (List String) → Nat → ProgHOL 64 → ProgHOL 64
  | [], _, rest => rest
  | cs :: css, i, rest => nameP C cs (.seq (.store (.op .add [vv bv, .const (BitVec.ofNat 64 (8 * i))]) (vv vPn))
      (namesP C bv css (i + 1) rest))

theorem namesP_congr {C C' : Ctx} (h1 : C.HB = C'.HB) (h2 : C.HN = C'.HN) (bv : MlS) :
    ∀ (css : List (List String)) (i : Nat) (r : ProgHOL 64), namesP C bv css i r = namesP C' bv css i r
  | [], _, _ => rfl
  | cs :: css, i, r => by simp only [namesP]; rw [namesP_congr h1 h2 bv css (i + 1) r, nameP_congr h1 h2]

def NamesOK : List ConLeche.Name → List (List String) → Prop
  | [], [] => True
  | n :: ns, cs :: css => strComps n = some cs ∧ compsOK cs ∧ NamesOK ns css
  | _, _ => False

set_option maxHeartbeats 2000000 in
theorem names_spec {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (code : Code)
    (hcN : code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one))
    (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D) {rest : ProgHOL 64} {R : β → BitVec 64 → AState → PState σ → Prop}
    (H : List (BitVec 64)) (b : Nat) (hb : 64 ≤ b) (bv : MlS) (hbv1 : bv ≠ vPn) (hbv2 : bv ≠ vKa) :
    ∀ (ns : List ConLeche.Name) (css : List (List String)) (i : Nat) (EH : List (BitVec 64)) (s : AState) (Γ : Env)
      (M : Mem) (k : List NIdx → AM β), NamesOK ns css → (∀ j, j < 64 → EH[j]? = EH0[j]?) →
    Γ.get bv = some (ecell (Cb code H EH) b) → b + i + ns.length ≤ EH.length →
    (∀ hs s' (EH' : List (BitVec 64)) (Γ' : Env), EH'.length = EH.length → (∀ j, j < b + i → EH'[j]? = EH[j]?) →
      (∀ j (hj : j < ns.length), EH'[b + i + j]? = some (Enc.idxW (hs[j]?.getD default))) →
      (∀ y, y ≠ vPn → y ≠ vKa → Γ'.get y = Γ.get y) → internNameList ns s = .ok (hs, s') →
      SpecR (Inv (Cb code H EH') s' Γ' [] D) rest s' (k hs) R) →
    SpecR (Inv (Cb code H EH) s Γ M D) (namesP (Cb code H EH) bv css i rest) s (internNameList ns >>= k) R
  | [], [], i, EH, s, Γ, M, k, _, hEH, hpb, hroom, hk => by
    simp only [namesP, internNameList, pure_bind]
    intro t ht
    exact hk [] s EH Γ rfl (fun _ _ => rfl) (fun j hj => absurd hj (by simp)) (fun _ _ _ => rfl) rfl t
      ⟨ht.sr, ht.env, fun _ _ h => absurd h (by simp), ht.decl⟩
  | n :: ns, cs :: css, i, EH, s, Γ, M, k, hok3, hEH, hpb, hroom, hk => by
    obtain ⟨hcs, hcok, hrest⟩ := hok3
    simp only [List.length_cons] at hroom
    have e : (internNameList (n :: ns) >>= k) =
        (internName n >>= fun h => internNameList ns >>= fun hs => k (h :: hs)) := by
      simp only [internNameList, bind_assoc, pure_bind]
    rw [e]
    simp only [namesP]
    intro t ht
    have hst : StateOK s := ⟨ht.sr.twf⟩
    have hd : denoteN s.store.ns default = some .anonymous :=
      denoteN_ext (boot_ok P0).2.2.1 ht.sr.floor
    refine name_spec ra (Cb code H EH) (ctxOK_Cb code H EH hEH) (frontOK_Cb code H EH) hcN D hPn hKa n cs hcs hcok
      s hst hd Γ M _ (fun h s1 Γ1 hag hpn hr => ?_) t ht
    have hpb1 : Γ1.get bv = some (ecell (Cb code H EH) b) := by rw [hag _ hbv1 hbv2]; exact hpb
    refine specR_envStoreI (ctxOK_Cb code H EH hEH) (.op .add [vv bv, .const (BitVec.ofNat 64 (8 * i))]) (vv vPn)
      (b + i) (by rw [Cb_EH]; omega) (Enc.idxW h)
      (by simp only [sev, vv, hpb1, Option.bind_eq_bind, Option.bind_some, Option.pure_def]; rw [ecell_add])
      (by simp [sev, vv, hpn]) ?_
    rw [ctxE_Cb, Cb_EH, namesP_congr (Cb_HB code H EH H (EH.set (b + i) (Enc.idxW h)))
      (Cb_HN code H EH H (EH.set (b + i) (Enc.idxW h))) bv]
    refine names_spec ra code hcN D hPn hKa H b hb bv hbv1 hbv2 ns css (i + 1) _ s1 Γ1 [] _ hrest
      (fun j hj => by rw [List.getElem?_set, ite_eq_right (by omega)]; exact hEH j hj) (by rw [hpb1]; rfl)
      (by simp only [List.length_set]; omega) (fun hs s2 EH2 Γ2 hl2 h1 h2 hag2 hr2 => ?_)
    refine hk (h :: hs) s2 EH2 Γ2 (by rw [hl2]; simp) (fun j hj => by rw [h1 j (by omega), List.getElem?_set, ite_eq_right (by omega)])
      (fun j hj => ?_) (fun y h1' h2' => by rw [hag2 y h1' h2', hag y h1' h2']) ?_
    · cases j with
      | zero =>
        rw [Nat.add_zero, h1 (b + i) (by omega), List.getElem?_set_self (by omega)]; rfl
      | succ j =>
        rw [show b + i + (j + 1) = b + (i + 1) + j by omega, h2 j (by simpa using hj)]; rfl
    · simp only [internNameList, bind, StateT.bind, Except.bind, hr, hr2, pure, StateT.pure, Except.pure]

end ConPanqueque.Start
