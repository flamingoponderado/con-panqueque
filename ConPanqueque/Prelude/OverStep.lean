import ConPanqueque.Prelude.Keep

/-! # The override pass's pieces: a prelude record's key, and record equality

* `keyP`: the key handle of the record at `ovP` (a value record's name; a block's first member's
  name), hanging on an empty block (`keyP_step`);
* `recEqP`: hang unless the value record at `ovD` has the same cells as the record at `ovP`
  (`recEqP_step`: then they are the same `IDeclaration`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

def ovN := ofString "ov_n"
def ovNP := ofString "ov_np"
def ovJ := ofString "ov_j"
def ovK := ofString "ov_k"
def ovW := ofString "ov_w"
def ovP := ofString "ov_p"
def ovD := ofString "ov_d"
def ovT := ofString "ov_t"
def ovB := ofString "ov_b"
def ovO := ofString "ov_o"
def ovKey := ofString "ov_key"
def ovNm := ofString "ov_nm"
def ovDrop := ofString "ov_drop"
def ovA := ofString "ov_a"
def ovB2 := ofString "ov_b2"
def ovI := ofString "ov_i"
def ovX := ofString "ov_x"
def ovY := ofString "ov_y"
def ovKA := ofString "ov_ka"
def ovFL := ofString "ov_fl"
def ovR2 := ofString "ov_r2"
def ovQ := ofString "ov_q"
def ovQN := ofString "ov_qn"
def ovQB := ofString "ov_qb"
def ovQX := ofString "ov_qx"
def ovM := ofString "ov_m"
def ovMN := ofString "ov_mn"
def ovMA := ofString "ov_ma"
def ovMB := ofString "ov_mb"
def ovCX := ofString "ov_cx"
def ovCY := ofString "ov_cy"
def ovCT := ofString "ov_ct"
def ovRI := ofString "ov_ri"
def ovRN := ofString "ov_rn"
def ovRA := ofString "ov_ra"
def ovRB := ofString "ov_rb"
def ovRX := ofString "ov_rx"
def ovRY := ofString "ov_ry"

/-- The pass's locals. -/
def ovVars : List MlS := [ovN, ovNP, ovJ, ovK, ovW, ovP, ovD, ovT, ovB, ovO, ovKey, ovNm, ovDrop, ovA, ovB2, ovI,
  ovX, ovY, ovKA, ovFL, ovR2, ovQ, ovQN, ovQB, ovQX, ovM, ovMN, ovMA, ovMB, ovCX, ovCY, ovCT, ovRI, ovRN, ovRA, ovRB,
  ovRX, ovRY]

/-- `x + 8 k`. -/
def offE (x : MlS) (k : Nat) : ExpHOL 64 := .op .add [vv x, .const (BitVec.ofNat 64 (8 * k))]

/-- `x + 8 y + 8 k`. -/
def slotE (x y : MlS) (k : Nat) : ExpHOL 64 :=
  .op .add [vv x, .op .add [.shift .lsl (vv y) (.const 3), .const (BitVec.ofNat 64 (8 * k))]]

theorem sev_off (Γ : Env) (C : Ctx) (x : MlS) (o k : Nat) (hx : Γ.get x = some (cellA C o)) :
    sev Γ (offE x k) = some (cellA C (o + k)) := by
  simp only [offE, sev, vv, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def, cellA_add]

theorem sev_slot (Γ : Env) (C : Ctx) (x y : MlS) (o i k : Nat) (hx : Γ.get x = some (cellA C o))
    (hy : Γ.get y = some (BitVec.ofNat 64 i)) (hi : 8 * i < 2 ^ 64) :
    sev Γ (slotE x y k) = some (cellA C (o + k + i)) := by
  simp only [slotE, sev, vv, hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
    show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, ite_true]
  rw [shl3 i hi, show o + k + i = o + (i + k) by omega, cellA_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.mul_add, Nat.add_mod]

theorem sev_eqC (Γ : Env) (x : MlS) (n : Nat) (a : BitVec 64) (hx : Γ.get x = some a) :
    sev Γ (.cmp .equal (vv x) (.const (BitVec.ofNat 64 n))) = some (if a = BitVec.ofNat 64 n then 1 else 0) :=
  ConPanqueque.Start.sev_eqW Γ (vv x) (.const _) a _ (by simpa [sev, vv] using hx) rfl

theorem ite10_ne {p : Prop} [Decidable p] (h : (if p then (1 : BitVec 64) else 0) ≠ 0) : p := by
  by_cases e : p
  · exact e
  · simp [e] at h

theorem ite10_eq {p : Prop} [Decidable p] (h : (if p then (1 : BitVec 64) else 0) = 0) : ¬ p := by
  intro e; simp [e] at h

theorem step_cont {P Q R : PState σ → Prop} {c1 c2 : ProgHOL 64} (h1 : Step P c1 Q)
    (h2 : ∀ t, Q t → Step (fun u => u = t) c2 R) : Step P (.seq c1 c2) R :=
  step_seq h1 (fun t ht => h2 t ht t rfl)

theorem step_here {P R : PState σ → Prop} {c : ProgHOL 64} {t : PState σ} (h : Step P c R) (ht : P t) :
    Step (fun u => u = t) c R := fun u hu => by subst hu; exact h u ht

theorem specR_cont {α : Type} {P Q : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h1 : Step P c1 Q)
    (h2 : ∀ t, Q t → SpecR (fun u => u = t) c2 s m R) : SpecR P (.seq c1 c2) s m R :=
  specR_step h1 (fun t ht => h2 t ht t rfl)

theorem specR_here {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} {t : PState σ} (h : SpecR P c s m R) (ht : P t) :
    SpecR (fun u => u = t) c s m R := fun u hu => by subst hu; exact h u ht

theorem specR_loadW {α : Type} {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (j : Nat) (w : BitVec 64)
    (hw : C.H[j]? = some w) (hx : x ∈ D) (he : sev Γ e = some (cellA C j))
    (h : SpecR (Inv C s ((x, w) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ [] D) (.seq (.assign .local x (.load .one e)) rest) s m R := by
  have hj : j < C.H.length := by
    by_cases hj : j < C.H.length
    · exact hj
    · rw [List.getElem?_eq_none (by omega)] at hw; cases hw
  refine specR_heapLoadI x e j hj hx he ?_
  have : C.H[j] = w := by rw [List.getElem?_eq_getElem hj] at hw; exact Option.some.inj hw
  rw [this]; exact h

theorem lt_of_get {H : List (BitVec 64)} {j : Nat} {w : BitVec 64} (h : H[j]? = some w) : j < H.length := by
  by_cases hj : j < H.length
  · exact hj
  · rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem getElem_of_get {H : List (BitVec 64)} {j : Nat} {w : BitVec 64} (h : H[j]? = some w) :
    H[j]'(lt_of_get h) = w := by
  rw [List.getElem?_eq_getElem (lt_of_get h)] at h; exact Option.some.inj h

/-- `x := *(e)` at a cell whose word is known. -/
theorem step_loadW {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (x : MlS) (e : ExpHOL 64) (j : Nat)
    (w : BitVec 64) (hw : C.H[j]? = some w) (hx : x ∈ D) (he : sev Γ e = some (cellA C j)) :
    Step (Inv (σ := σ) C s Γ [] D) (.assign .local x (.load .one e)) (Inv C s ((x, w) :: Γ) [] D) := by
  have := T.step_heapLoadI (σ := σ) (C := C) (s := s) (M := []) x e j (lt_of_get hw) hx he
  rwa [getElem_of_get hw] at this

theorem name_cons_val (ci : IConstantInfo) : ci.name = ci.toConstantVal.name := by
  cases ci <;> rfl

/-- The key: a value record's name, a block's first member's name. -/
def keyP : ProgHOL 64 :=
  .seq (.assign .local ovT (.load .one (vv ovP)))
  (.ite (.cmp .equal (vv ovT) (.const 4))
    (.seq (.assign .local ovB (.load .one (offE ovP 2)))
    (.seq (.assign .local ovO (.load .one (vv ovB)))
    (.seq (.ite (.cmp .equal (vv ovO) (.const 0)) hang .skip)
    (.seq (.assign .local ovO (.load .one (offE ovB 1)))
      (.assign .local ovKey (.load .one (offE ovO 1)))))))
    (.assign .local ovKey (.load .one (offE ovP 1))))

theorem get_cons_ne (Γ : Env) (x y : MlS) (v : BitVec 64) (h : y ≠ x) : T.Env.get ((x, v) :: Γ) y = Γ.get y := by
  simp (config := {decide := true}) [T.Env.get_cons, h]

theorem keyP_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F o : Nat} {p : IDeclaration} (hr : RecEnc C F C.H o p) (hP : Γ.get ovP = some (cellA C o)) :
    Step (Inv (σ := σ) C s Γ [] D) keyP (fun t => ∃ k Γ', p.names.head? = some k ∧
      (∀ y, y ≠ ovT → y ≠ ovB → y ≠ ovO → y ≠ ovKey → Γ'.get y = Γ.get y) ∧
      Γ'.get ovKey = some (Enc.idxW k) ∧ Inv C s Γ' [] D t) := by
  have hT := recEnc_tag hr
  refine step_seq (step_loadW ovT (vv ovP) o _ hT (hD _ (by simp [ovVars])) (by simpa [sev, vv] using hP)) ?_
  refine step_ifI _ _ (sev_eqC _ ovT 4 (BitVec.ofNat 64 (tagOf p)) (by simp (config := {decide := true}) [T.Env.get_cons])) (fun h4 => ?_)
    (fun h4 => ?_)
  · -- a block
    have ht4 : tagOf p = 4 := by
      by_contra hne
      have := tagOf_lt p
      apply h4; rw [if_neg]; intro e
      exact hne (tagOf_inj (tagOf_lt p) (by omega) e)
    cases p with
    | indDecl block nP =>
      obtain ⟨-, -, -, -, ob, hob, h3, h4', -⟩ := hr
      obtain ⟨os, hlen, hblk, hcie⟩ := h4' C.H (fun _ _ _ h => h)
      refine step_seq (step_loadW ovB (offE ovP 2) (o + 2) _ h3 (hD _ (by simp [ovVars]))
        (sev_off _ C ovP o 2 (by simp (config := {decide := true}) [T.Env.get_cons, hP]))) ?_
      have hB : T.Env.get ((ovB, cellA C ob) :: (ovT, BitVec.ofNat 64 (tagOf (IDeclaration.indDecl block nP))) :: Γ)
          ovB = some (cellA C (ob + 0)) := by simp (config := {decide := true}) [T.Env.get_cons]
      refine step_seq (step_loadW ovO (vv ovB) ob _ hblk.1 (hD _ (by simp [ovVars])) (by simpa [sev, vv] using hB)) ?_
      let Γb : Env := (ovO, BitVec.ofNat 64 (List.map (cellA C) os).length) :: (ovB, cellA C ob) ::
        (ovT, BitVec.ofNat 64 (tagOf (IDeclaration.indDecl block nP))) :: Γ
      refine step_cont (Q := fun t => block ≠ [] ∧ Inv C s Γb [] D t)
        (step_ifI _ _ (sev_eqC _ ovO 0 (BitVec.ofNat 64 (List.map (cellA C) os).length)
          (by simp (config := {decide := true}) [T.Env.get_cons]))
        (fun _ => step_hangI) (fun h0 => fun t ht => (step_skipI t ht).imp id (fun ⟨a, b⟩ => ⟨a, fun e => by
          subst e; simp at hlen; subst hlen; exact ite10_eq h0 rfl, b⟩))) (fun t ⟨hne, htb⟩ => ?_)
      refine step_here ?_ htb
      have hos : 0 < os.length := by
        rw [hlen]; cases block with
        | nil => exact absurd rfl hne
        | cons _ _ => simp
      have hb0 := hblk.2 0 (by simpa using hos)
      try simp only [List.getElem_map] at hb0
      refine step_seq (step_loadW ovO (offE ovB 1) (ob + 1 + 0) _ hb0 (hD _ (by simp [ovVars]))
        (sev_off _ C ovB ob _ (by simp (config := {decide := true}) [Γb, T.Env.get_cons]))) ?_
      have hc := hcie 0 (by rw [← hlen]; exact hos) hos
      have hn := hc.1.1
      refine fun t ht => (step_loadW ovKey (offE ovO 1) (os[0] + 1) _ hn (hD _ (by simp [ovVars]))
        (sev_off _ C ovO _ 1 (by simp (config := {decide := true}) [T.Env.get_cons])) t ht).imp id (fun ⟨hn', hq⟩ => ⟨hn', ?_⟩)
      refine ⟨block[0].name, _, ?_, ?_, by simp (config := {decide := true}) [T.Env.get_cons, name_cons_val], hq⟩
      · cases block with
        | nil => exact absurd rfl hne
        | cons b bs => simp [IDeclaration.names]
      · intro y h1 h2 h3 h4
        simp (config := {decide := true}) [Γb, T.Env.get_cons, h1, h2, h3, h4]
    | _ => simp [tagOf] at ht4
  · -- a value record
    have hv : isVal p = true := by
      cases p <;> simp_all [isVal, tagOf]
    have hcv := recEnc_cv hr hv
    obtain ⟨ol, -, hn, -⟩ := hcv
    refine fun t ht => (step_loadW ovKey (offE ovP 1) (o + 1) _ hn (hD _ (by simp [ovVars]))
      (sev_off _ C ovP o 1 (by simp (config := {decide := true}) [T.Env.get_cons, hP])) t ht).imp id
      (fun ⟨hn', hq⟩ => ⟨hn', ?_⟩)
    refine ⟨(cvOf p).name, _, by rw [names_val hv, valName_cvOf p hv]; rfl, ?_, by simp (config := {decide := true}) [T.Env.get_cons], hq⟩
    intro y h1 h2 h3 h4
    simp (config := {decide := true}) [T.Env.get_cons, h1, h4]

theorem regAt {C : Ctx} {F rb capD : Nat} {decls : Array IDeclaration} (hdr : DeclsRel C F rb capD C.H decls)
    (k : Nat) (hk : k < decls.size) : ∃ o, C.H[rb + 1 + k]? = some (cellA C o) ∧ RecEnc C F C.H o decls[k] :=
  hdr.2.2.2.2 k hk

theorem name_of_val {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d)
    (hv : isVal d = true) : H[o + 1]? = some (Enc.idxW (valName d)) := by
  obtain ⟨ol, -, hn, -⟩ := recEnc_cv h hv
  rw [valName_cvOf d hv]; exact hn

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

/-- Hang unless the words at `ovD + 8k` and `ovP + 8k` agree. -/
def cmpAt (k : Nat) : ProgHOL 64 :=
  .seq (.assign .local ovX (.load .one (offE ovD k)))
  (.seq (.assign .local ovY (.load .one (offE ovP k)))
    (.ite (.cmp .equal (vv ovX) (vv ovY)) .skip hang))

/-- One step of the level-parameter comparison. -/
def lpBody : ProgHOL 64 :=
  .seq (.assign .local ovA (offE ovA 1))
  (.seq (.assign .local ovB2 (offE ovB2 1))
  (.seq (.assign .local ovY (.load .one (vv ovA)))
  (.seq (.assign .local ovT (.load .one (vv ovB2)))
  (.seq (.ite (.cmp .equal (vv ovY) (vv ovT)) .skip hang)
    (.assign .local ovI (.op .add [vv ovI, .const 1]))))))

/-- The level-parameter blocks at `ovA` and `ovB2` (advanced in place) hold the same words. -/
def lpEqP : ProgHOL 64 :=
  .seq (.assign .local ovX (.load .one (vv ovA)))
  (.seq (.assign .local ovY (.load .one (vv ovB2)))
  (.seq (.ite (.cmp .equal (vv ovX) (vv ovY)) .skip hang)
  (.seq (.assign .local ovI (.const 0))
    (.while (.cmp .lower (vv ovI) (vv ovX)) lpBody))))

/-- Hang unless the value record at `ovD` has the record at `ovP`'s cells. -/
def recEqP : ProgHOL 64 :=
  .seq (cmpAt 0)
  (.seq (cmpAt 1)
  (.seq (cmpAt 3)
  (.seq (.assign .local ovA (.load .one (offE ovD 2)))
  (.seq (.assign .local ovB2 (.load .one (offE ovP 2)))
  (.seq lpEqP
  (.seq (.assign .local ovT (.load .one (vv ovD)))
  (.seq (.ite (.cmp .equal (vv ovT) (.const 5)) .skip (cmpAt 4))
    (.ite (.cmp .equal (vv ovT) (.const 1)) (cmpAt 5) .skip))))))))

theorem sev_eqv (Γ : Env) (x y : MlS) (a b : BitVec 64) (hx : Γ.get x = some a) (hy : Γ.get y = some b) :
    sev Γ (.cmp .equal (vv x) (vv y)) = some (if a = b then 1 else 0) :=
  ConPanqueque.Start.sev_eqW Γ (vv x) (vv y) a b (by simpa [sev, vv] using hx) (by simpa [sev, vv] using hy)

/-- `cmpAt k` at two records' cells. -/
theorem cmpAt_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {od op : Nat} (hd : Γ.get ovD = some (cellA C od)) (hp : Γ.get ovP = some (cellA C op)) (k : Nat)
    (a b : BitVec 64) (ha : C.H[od + k]? = some a) (hb : C.H[op + k]? = some b) :
    Step (Inv (σ := σ) C s Γ [] D) (cmpAt k) (fun t => a = b ∧ Inv C s ((ovY, b) :: (ovX, a) :: Γ) [] D t) := by
  refine step_seq (step_loadW ovX (offE ovD k) (od + k) a ha (hD _ (by simp [ovVars])) (sev_off _ C ovD od k hd)) ?_
  refine step_seq (step_loadW ovY (offE ovP k) (op + k) b hb (hD _ (by simp [ovVars]))
    (sev_off _ C ovP op k (by rw [get_cons_ne _ _ _ _ (by decide)]; exact hp))) ?_
  refine step_ifI _ _ (sev_eqv _ ovX ovY a b (by simp (config := {decide := true}) [T.Env.get_cons]) (by simp (config := {decide := true}) [T.Env.get_cons]))
    (fun h => ?_) (fun _ => step_hangI)
  exact fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, ite10_ne h, h2⟩)

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

/-- A loop as a step, with an invariant over the context and the environment. -/
theorem step_whileCE {s : AState} {D : List MlS} (c : ExpHOL 64) (body : ProgHOL 64)
    (I Q : Ctx → Env → Prop) (C0 : Ctx) (Γ0 : Env) (h0 : I C0 Γ0)
    (hc : ∀ C Γ, I C Γ → ∃ w, sev Γ c = some w ∧ (w = 0 → Q C Γ) ∧
      (w ≠ 0 → Step (σ := σ) (Inv C s Γ [] D) body (fun t => ∃ C' Γ', I C' Γ' ∧ Inv C' s Γ' [] D t))) :
    Step (σ := σ) (Inv C0 s Γ0 [] D) (.while c body) (fun t => ∃ C Γ, Q C Γ ∧ Inv C s Γ [] D t) := by
  intro t ht
  exact while_stop (σ := σ) c body (fun u => ∃ C Γ, I C Γ ∧ Inv C s Γ [] D u)
    (fun u => ∃ C Γ, Q C Γ ∧ Inv C s Γ [] D u)
    (by
      intro u ⟨C, Γ, hI, hu⟩
      obtain ⟨w, hw, h0', h1⟩ := hc C Γ hI
      refine ⟨w, ?_, fun e => ⟨C, Γ, h0' e, hu⟩, fun hn _ => ?_⟩
      · simp only [evalHOLFinite]; exact inv_ev hu hw
      · exact h1 hn _ (inv_decClock hu)) t ⟨C0, Γ0, h0, ht⟩

theorem sev_lowerV (Γ : Env) (x y : MlS) (a b : Nat) (hx : Γ.get x = some (BitVec.ofNat 64 a))
    (hy : Γ.get y = some (BitVec.ofNat 64 b)) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    sev Γ (.cmp .lower (vv x) (vv y)) = some (bw (a < b)) :=
  sev_lower Γ (vv x) (vv y) a b (by simpa [sev, vv] using hx) (by simpa [sev, vv] using hy) ha hb

theorem bw_ne0' {p : Prop} [Decidable p] (h : bw p ≠ 0) : p := by
  by_cases e : p
  · exact e
  · simp [bw, e] at h

theorem bw_eq0' {p : Prop} [Decidable p] (h : bw p = 0) : ¬ p := by
  intro e; simp [bw, e] at h

theorem sev_succV (Γ : Env) (x : MlS) (i : Nat) (hx : Γ.get x = some (BitVec.ofNat 64 i)) :
    sev Γ (.op .add [vv x, .const 1]) = some (BitVec.ofNat 64 (i + 1)) := by
  simp only [sev, vv, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- The locals `lpEqP` writes. -/
def lpMods : List MlS := [ovX, ovY, ovI, ovA, ovB2, ovT]

/-- `lpEqP` at two blocks: it returns only if they hold the same words. -/
theorem lpEq_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {ol ol' : Nat} {xs ys : List (BitVec 64)} (hx : BlkAt C.H ol xs) (hy : BlkAt C.H ol' ys)
    (hx59 : xs.length < 2 ^ 63) (hy59 : ys.length < 2 ^ 63)
    (ha : Γ.get ovA = some (cellA C ol)) (hb : Γ.get ovB2 = some (cellA C ol')) :
    Step (Inv (σ := σ) C s Γ [] D) lpEqP (fun t => C.H[ol]? = C.H[ol']? ∧
      (∀ i, i < xs.length → C.H[ol + 1 + i]? = C.H[ol' + 1 + i]?) ∧
      ∃ Γ', (∀ y, y ∉ lpMods → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t) := by
  refine step_seq (step_loadW ovX (vv ovA) ol _ hx.1 (hD _ (by simp [ovVars])) (by simpa [sev, vv] using ha)) ?_
  refine step_seq (step_loadW ovY (vv ovB2) ol' _ hy.1 (hD _ (by simp [ovVars]))
    (by simp only [sev, vv]; rw [get_cons_ne _ _ _ _ (by decide)]; exact hb)) ?_
  refine step_seq (Q := fun t => xs.length = ys.length ∧ Inv C s ((ovY, BitVec.ofNat 64 ys.length) ::
      (ovX, BitVec.ofNat 64 xs.length) :: Γ) [] D t)
    (step_ifI _ _ (sev_eqv _ ovX ovY (BitVec.ofNat 64 xs.length) (BitVec.ofNat 64 ys.length) (by simp (config := {decide := true}) [T.Env.get_cons]) (by simp (config := {decide := true}) [T.Env.get_cons]))
      (fun h => fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, ofNat_inj63 (by omega) (by omega)
        (ite10_ne h), h2⟩)) (fun _ => step_hangI)) ?_
  intro t ⟨hl, ht⟩
  have hn0 : C.H[ol]? = C.H[ol']? := by rw [hx.1, hy.1, hl]
  let Γ1 : Env := (ovY, BitVec.ofNat 64 ys.length) :: (ovX, BitVec.ofNat 64 xs.length) :: Γ
  have g1 : ∀ y, y ∉ lpMods → Γ1.get y = Γ.get y := by
    intro y hy; simp only [lpMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp (config := {decide := true}) [Γ1, T.Env.get_cons, hy.1, hy.2.1]
  have := step_seq (step_assignI (C := C) (s := s) (M := []) (D := D) ovI (.const 0) 0 (hD _ (by simp [ovVars])) rfl)
    (step_whileCE (s := s) (D := D) (.cmp .lower (vv ovI) (vv ovX)) lpBody
      (fun C' Γ' => C' = C ∧ ∃ i, i ≤ xs.length ∧ Γ'.get ovI = some (BitVec.ofNat 64 i) ∧
        Γ'.get ovA = some (cellA C (ol + i)) ∧ Γ'.get ovB2 = some (cellA C (ol' + i)) ∧
        Γ'.get ovX = some (BitVec.ofNat 64 xs.length) ∧
        (∀ i', i' < i → C.H[ol + 1 + i']? = C.H[ol' + 1 + i']?) ∧ (∀ y, y ∉ lpMods → Γ'.get y = Γ.get y))
      (fun C' Γ' => C' = C ∧ (∀ i, i < xs.length → C.H[ol + 1 + i]? = C.H[ol' + 1 + i]?) ∧
        (∀ y, y ∉ lpMods → Γ'.get y = Γ.get y))
      C ((ovI, 0) :: Γ1) ⟨rfl, 0, Nat.zero_le _, by simp (config := {decide := true}) [T.Env.get_cons],
        by simp (config := {decide := true}) [Γ1, T.Env.get_cons, ha],
        by simp (config := {decide := true}) [Γ1, T.Env.get_cons, hb],
        by simp (config := {decide := true}) [Γ1, T.Env.get_cons], fun i' h => absurd h (by omega),
        fun y hy => by
          have : y ≠ ovI := fun e => hy (by simp [e, lpMods])
          simp only [T.Env.get_cons, this, ite_false]; exact g1 y hy⟩ ?_) t ht
  · rcases this with hs | ⟨hn, C', Γ', ⟨rfl, hall, hag⟩, hq⟩
    · exact Or.inl hs
    · exact Or.inr ⟨hn, hn0, hall, Γ', hag, hq⟩
  intro C' Γ' ⟨hC, i, hi, gI, gA, gB, gX, hdone, hag⟩
  subst C'
  refine ⟨bw (i < xs.length), sev_lowerV _ _ _ _ _ gI gX (by omega) (by omega), fun h0 => ?_, fun h1 => ?_⟩
  · have : i = xs.length := by have := bw_eq0' h0; omega
    subst this; exact ⟨rfl, hdone, hag⟩
  · have hlt := bw_ne0' h1
    have hxi := hx.2 i hlt
    have hyi := hy.2 i (by omega)
    rw [show ol + 1 + i = ol + i + 1 by omega] at hxi
    rw [show ol' + 1 + i = ol' + i + 1 by omega] at hyi
    unfold lpBody
    refine step_seq (step_assignI ovA (offE ovA 1) _ (hD _ (by simp [ovVars])) (sev_off _ C ovA _ 1 gA)) ?_
    refine step_seq (step_assignI ovB2 (offE ovB2 1) _ (hD _ (by simp [ovVars]))
      (sev_off _ C ovB2 _ 1 (by rw [get_cons_ne _ _ _ _ (by decide)]; exact gB))) ?_
    refine step_seq (step_loadW ovY (vv ovA) _ _ hxi (hD _ (by simp [ovVars])) (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
    refine step_seq (step_loadW ovT (vv ovB2) _ _ hyi (hD _ (by simp [ovVars])) (by simp (config := {decide := true}) [sev, vv, T.Env.get_cons])) ?_
    refine step_seq (Q := fun t => xs[i] = ys[i] ∧ _) (step_ifI _ _ (sev_eqv _ ovY ovT xs[i] ys[i]
      (by simp (config := {decide := true}) [T.Env.get_cons]) (by simp (config := {decide := true}) [T.Env.get_cons]))
      (fun h => fun t ht => (step_skipI t ht).imp id (fun ⟨h1, h2⟩ => ⟨h1, ite10_ne h, h2⟩)) (fun _ => step_hangI)) ?_
    intro t ⟨he, ht⟩
    refine (step_assignI ovI (.op .add [vv ovI, .const 1]) _ (hD _ (by simp [ovVars])) (sev_succV _ ovI i
      (by simp (config := {decide := true}) [T.Env.get_cons]; exact gI)) t ht).imp id (fun ⟨hn, hq⟩ => ⟨hn, C, _, ⟨rfl, i + 1, by omega,
        by simp (config := {decide := true}) [T.Env.get_cons],
        by simp (config := {decide := true}) [T.Env.get_cons, Nat.add_assoc],
        by simp (config := {decide := true}) [T.Env.get_cons, Nat.add_assoc],
        by simp (config := {decide := true}) [T.Env.get_cons]; exact gX, fun i' hi' => ?_, fun y hy => ?_⟩, hq⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
      · exact hdone i' h
      · rw [hx.2 i' hlt, hy.2 i' (by omega), he]
    · simp only [lpMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp (config := {decide := true}) [T.Env.get_cons, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]; exact hag y (by
        simp [lpMods, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2])

end ConPanqueque.Prelude

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

variable {σ : Type}

theorem recEnc_f4 {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d)
    (hv : isVal d = true) : ∃ w, H[o + 4]? = some w := by
  cases d with
  | defnDecl => exact ⟨_, h.2.2.2.1⟩
  | thmDecl => exact ⟨_, h.2.2.2⟩
  | opaqueDecl => exact ⟨_, h.2.2.2⟩
  | axiomDecl => exact h.2.2.2.1
  | quotDecl => exact ⟨_, h.2.2.2⟩
  | indDecl => simp [isVal] at hv

theorem recEnc_f5 {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d)
    (h1 : tagOf d = 1) : ∃ w, H[o + 5]? = some w := by
  cases d with
  | defnDecl => exact ⟨_, h.2.2.2.2.1⟩
  | _ => simp [tagOf] at h1

theorem isVal_of_tag {d : IDeclaration} (h : tagOf d ≠ 4) : isVal d = true := by
  cases d <;> simp_all [tagOf, isVal]

theorem tag_ne4 {d : IDeclaration} (h : isVal d = true) : tagOf d ≠ 4 := by
  cases d <;> simp_all [tagOf, isVal]

/-- The locals `recEqP` writes. -/
def recMods : List MlS := [ovX, ovY, ovI, ovA, ovB2, ovT]

theorem cmpAt_step' {C : Ctx} {s : AState} {Γ0 Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {od op : Nat} (hd : Γ0.get ovD = some (cellA C od)) (hp : Γ0.get ovP = some (cellA C op))
    (hag : ∀ y, y ∉ recMods → Γ.get y = Γ0.get y) (k : Nat)
    (a b : BitVec 64) (ha : C.H[od + k]? = some a) (hb : C.H[op + k]? = some b) :
    Step (Inv (σ := σ) C s Γ [] D) (cmpAt k) (fun t => a = b ∧ ∃ Γ', (∀ y, y ∉ recMods → Γ'.get y = Γ0.get y) ∧
      Inv C s Γ' [] D t) :=
  fun t ht => (cmpAt_step hD (by rw [hag _ (by decide)]; exact hd) (by rw [hag _ (by decide)]; exact hp) k a b ha hb t
    ht).imp id (fun ⟨hn, he, hq⟩ => ⟨hn, he, _, fun y hy => by
      simp only [recMods, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [T.Env.get_cons, hy.1, hy.2.1, ite_false]; exact hag y (by
        simp [recMods, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]), hq⟩)

/-- **`recEqP`**: it returns only if the value record at `ovD` is the record at `ovP`. -/
theorem recEqP_step {C : Ctx} {s : AState} {Γ : Env} {D : List MlS} (hD : ∀ x ∈ ovVars, x ∈ D)
    {F od op : Nat} {d p : IDeclaration} (hrd : RecEnc C F C.H od d) (hrp : RecEnc C F C.H op p)
    (hv : isVal d = true) (hd : Γ.get ovD = some (cellA C od)) (hp : Γ.get ovP = some (cellA C op)) :
    Step (Inv (σ := σ) C s Γ [] D) recEqP (fun t => d = p ∧ ∃ Γ', (∀ y, y ∉ recMods → Γ'.get y = Γ.get y) ∧
      Inv C s Γ' [] D t) := by
  have hag0 : ∀ y, y ∉ recMods → Γ.get y = Γ.get y := fun _ _ => rfl
  -- the kinds
  refine step_cont (cmpAt_step' hD hd hp hag0 0 _ _ (recEnc_tag hrd) (recEnc_tag hrp))
    (fun t ⟨htag, Γ1, hag1, ht1⟩ => ?_)
  have et : tagOf d = tagOf p := tagOf_inj (tagOf_lt d) (tagOf_lt p) htag
  have hvp : isVal p = true := isVal_of_tag (by rw [← et]; exact tag_ne4 hv)
  obtain ⟨ol, -, hn, hl, hty, hblk, h59⟩ := recEnc_cv hrd hv
  obtain ⟨ol', -, hn', hl', hty', hblk', h59'⟩ := recEnc_cv hrp hvp
  refine step_here ?_ ht1
  refine step_cont (cmpAt_step' hD hd hp hag1 1 _ _ hn hn') (fun t ⟨hne, Γ2, hag2, ht2⟩ => ?_)
  refine step_here ?_ ht2
  refine step_cont (cmpAt_step' hD hd hp hag2 3 _ _ hty hty') (fun t ⟨htye, Γ3, hag3, ht3⟩ => ?_)
  refine step_here ?_ ht3
  refine step_seq (step_loadW ovA (offE ovD 2) (od + 2) _ hl (hD _ (by simp [ovVars]))
    (sev_off _ C ovD od 2 (by rw [hag3 _ (by decide)]; exact hd))) ?_
  refine step_seq (step_loadW ovB2 (offE ovP 2) (op + 2) _ hl' (hD _ (by simp [ovVars]))
    (sev_off _ C ovP op 2 (by rw [get_cons_ne _ _ _ _ (by decide), hag3 _ (by decide)]; exact hp))) ?_
  refine step_cont (lpEq_step hD hblk hblk' (by simp; omega) (by simp; omega)
    (by rw [get_cons_ne _ _ _ _ (by decide)]; simp (config := {decide := true}) [T.Env.get_cons]) (by simp (config := {decide := true}) [T.Env.get_cons])) (fun t ⟨hb0, hbe, Γ4, hag4, ht4⟩ => ?_)
  have hcv : cvOf d = cvOf p := cv_eq_at (C := C) hn hty hblk h59 hn' hty' hblk' h59'
    (by rw [hn, hn', hne]) (by rw [hty, hty', htye]) hb0 (fun i hi => hbe i (by simpa using hi))
  have g4 : ∀ y, y ∉ recMods → Γ4.get y = Γ.get y := by
    intro y hy
    rw [hag4 y (by simpa [lpMods, recMods] using hy)]
    have h1 : y ≠ ovB2 := fun e => hy (by simp [e, recMods])
    have h2 : y ≠ ovA := fun e => hy (by simp [e, recMods])
    simp only [T.Env.get_cons, h1, h2, ite_false]; exact hag3 y hy
  refine step_here ?_ ht4
  refine step_seq (step_loadW ovT (vv ovD) od _ (recEnc_tag hrd) (hD _ (by simp [ovVars]))
    (by simp only [sev, vv]; rw [g4 _ (by decide)]; exact hd)) ?_
  have g5 : ∀ y, y ∉ recMods → T.Env.get ((ovT, BitVec.ofNat 64 (tagOf d)) :: Γ4) y = Γ.get y := by
    intro y hy
    have : y ≠ ovT := fun e => hy (by simp [e, recMods])
    simp only [T.Env.get_cons, this, ite_false]; exact g4 y hy
  have hD5 : T.Env.get ((ovT, BitVec.ofNat 64 (tagOf d)) :: Γ4) ovD = some (cellA C od) := by
    rw [g5 _ (by decide)]; exact hd
  have hP5 : T.Env.get ((ovT, BitVec.ofNat 64 (tagOf d)) :: Γ4) ovP = some (cellA C op) := by
    rw [g5 _ (by decide)]; exact hp
  -- the field at `o + 4`
  refine step_seq (Q := fun t => (tagOf d ≠ 5 → C.H[od + 4]? = C.H[op + 4]?) ∧ ∃ Γ', Γ'.get ovT =
      some (BitVec.ofNat 64 (tagOf d)) ∧ Γ'.get ovD = some (cellA C od) ∧ Γ'.get ovP = some (cellA C op) ∧
      (∀ y, y ∉ recMods → Γ'.get y = Γ.get y) ∧ Inv C s Γ' [] D t)
    (step_ifI _ _ (sev_eqC _ ovT 5 (BitVec.ofNat 64 (tagOf d)) (by simp (config := {decide := true}) [T.Env.get_cons])) (fun h5 => ?_)
      (fun h5 => ?_)) ?_
  · refine fun t ht => (step_skipI t ht).imp id (fun ⟨hn5, hq⟩ => ⟨hn5, fun hne5 => absurd ?_ hne5, _,
      by simp (config := {decide := true}) [T.Env.get_cons], hD5, hP5, g5, hq⟩)
    exact tagOf_inj (tagOf_lt d) (by omega) (ite10_ne h5)
  · obtain ⟨a, ha⟩ := recEnc_f4 hrd hv
    obtain ⟨b, hb⟩ := recEnc_f4 hrp hvp
    refine fun t ht => (cmpAt_step hD hD5 hP5 4 a b ha hb t ht).imp id (fun ⟨hn5, he, hq⟩ =>
      ⟨hn5, fun _ => by rw [ha, hb, he], _, by simp (config := {decide := true}) [T.Env.get_cons], (by simp (config := {decide := true}) [T.Env.get_cons, hD5]),
        (by simp (config := {decide := true}) [T.Env.get_cons, hP5]), fun y hy => ?_, hq⟩)
    have h1 : y ≠ ovY := fun e => hy (by simp [e, recMods])
    have h2 : y ≠ ovX := fun e => hy (by simp [e, recMods])
    simp only [T.Env.get_cons, h1, h2, ite_false]; exact g5 y hy
  intro t ⟨h4, Γ5, gT, gD, gP, hag5, ht5⟩
  refine (?_ : Step (Inv C s Γ5 [] D) _ (fun t => d = p ∧ ∃ Γ', (∀ y, y ∉ recMods → Γ'.get y = Γ.get y) ∧
      Inv C s Γ' [] D t)) t ht5
  -- the hint
  refine step_ifI _ _ (sev_eqC _ ovT 1 _ gT) (fun h1 => ?_) (fun h1 => ?_)
  · have e1 : tagOf d = 1 := tagOf_inj (tagOf_lt d) (by omega) (ite10_ne h1)
    obtain ⟨a, ha⟩ := recEnc_f5 hrd e1
    obtain ⟨b, hb⟩ := recEnc_f5 hrp (by rw [← et]; exact e1)
    refine fun t ht => (cmpAt_step hD gD gP 5 a b ha hb t ht).imp id (fun ⟨hn5, he, hq⟩ => ⟨hn5, ?_, _, fun y hy => ?_, hq⟩)
    · refine recEnc_eq hrd hrp hv hvp hcv (by rw [recEnc_tag hrd, recEnc_tag hrp, et])
        (fun h => h4 (fun e => h (by rw [recEnc_tag hrd, e]; rfl))) (fun _ => by rw [ha, hb, he])
    · have h1 : y ≠ ovY := fun e => hy (by simp [e, recMods])
      have h2 : y ≠ ovX := fun e => hy (by simp [e, recMods])
      simp only [T.Env.get_cons, h1, h2, ite_false]; exact hag5 y hy
  · have ne1 : tagOf d ≠ 1 := fun e => ite10_eq h1 (by rw [e])
    refine fun t ht => (step_skipI t ht).imp id (fun ⟨hn5, hq⟩ => ⟨hn5, ?_, Γ5, hag5, hq⟩)
    refine recEnc_eq hrd hrp hv hvp hcv (by rw [recEnc_tag hrd, recEnc_tag hrp, et])
      (fun h => h4 (fun e => h (by rw [recEnc_tag hrd, e]; rfl))) (fun h => absurd ?_ ne1)
    rw [recEnc_tag hrd] at h
    exact tagOf_inj (tagOf_lt d) (by omega) (Option.some.inj h)

end ConPanqueque.Prelude
