import ConPanqueque.T.Ex.StripPis
import ConPanqueque.T.LvlMk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `binderPair?`

Two λs (or two ∀s): their domains and bodies as a heap block `[4, ty₁, b₁, ty₂, b₂]`, or `0`.
-/

namespace ConPanqueque.T.ExBP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG ConPanqueque.T.ExPre
open ConPanqueque.T.ExA ConPanqueque.T.ExSP

def pLm := ofString "blm"
def pBa := ofString "bpa"
def pBb := ofString "bpb"
def bpParams : List MlS := [pLm, pBa, pBb]

def alloc5 (C : Ctx) (x : MlS) (e0 e1 e2 e3 e4 : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  allocP C x (.const 40) (.seq (.store (vv x) e0)
    (.seq (.store (.op .add [vv x, .const 8]) e1) (.seq (.store (.op .add [vv x, .const 16]) e2)
    (.seq (.store (.op .add [vv x, .const 24]) e3) (.seq (.store (.op .add [vv x, .const 32]) e4) rest)))))

/-- The image after writing five words at `H2.length …`. -/
def img5 (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 : BitVec 64) : List (BitVec 64) :=
  (((((H2 ++ ws).set H2.length w0).set (H2.length + 1) w1).set (H2.length + 2) w2).set (H2.length + 3) w3).set
    (H2.length + 4) w4

section
variable {σ : Type}

theorem specR_alloc5I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS)
    (e0 e1 e2 e3 e4 : ExpHOL 64) (w0 w1 w2 w3 w4 : BitVec 64) (hx : x ∈ D)
    (h0 : ∀ v, sev ((x, v) :: Γ) e0 = some w0) (h1 : ∀ v, sev ((x, v) :: Γ) e1 = some w1)
    (h2 : ∀ v, sev ((x, v) :: Γ) e2 = some w2) (h3 : ∀ v, sev ((x, v) :: Γ) e3 = some w3)
    (h4 : ∀ v, sev ((x, v) :: Γ) e4 = some w4)
    (hk : ∀ (H2 ws : List (BitVec 64)), C.H <+: H2 → ws.length = 5 →
      SpecR (Inv (ctxH C (img5 H2 ws w0 w1 w2 w3 w4)) s ((x, cellA C H2.length) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (alloc5 C x e0 e1 e2 e3 e4 rest) s m R := by
  unfold alloc5
  refine specR_allocI x _ 5 (by decide) hx (fun _ => rfl) (fun H2 ws hp hws hroom => ?_)
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) e0 H2.length (by simp [ctxH, hws]) w0 (by simp [cellA, ctxH])
    (h0 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e1 (H2.length + 1) (by simp [ctxH, hws]) w1
    (by simp [sev]; exact cellA_add_ofNat C H2.length 1) (h1 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e2 (H2.length + 2) (by simp [ctxH, hws]) w2
    (by simp [sev]; exact cellA_add_ofNat C H2.length 2) (h2 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e3 (H2.length + 3) (by simp [ctxH, hws]) w3
    (by simp [sev]; exact cellA_add_ofNat C H2.length 3) (h3 _) ?_
  refine specR_heapStoreI (ctxOK_H hok _) _ e4 (H2.length + 4) (by simp [ctxH, hws]) w4
    (by simp [sev]; exact cellA_add_ofNat C H2.length 4) (h4 _) ?_
  exact hk H2 ws hp hws

theorem img5_prefix (H2 ws : List (BitVec 64)) (w0 w1 w2 w3 w4 : BitVec 64) (h : ws.length = 5) :
    H2 <+: img5 H2 ws w0 w1 w2 w3 w4 :=
  prefix_of_get? (by simp [img5, h]) (fun k hk => by
    simp only [img5]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_append_left hk])

theorem img5_blk (H2 ws : List (BitVec 64)) (w1 w2 w3 w4 : BitVec 64) (h : ws.length = 5) :
    BlkAt (img5 H2 ws 4 w1 w2 w3 w4) H2.length [w1, w2, w3, w4] := by
  have hl : (H2 ++ ws).length = H2.length + 5 := by simp [h]
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [img5]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]; rfl
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · simp only [img5]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hl]; omega)]; rfl
    · simp only [img5]
      rw [show H2.length + 1 + 1 = H2.length + 2 by omega, List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hl]; omega)]; rfl
    · simp only [img5]
      rw [show H2.length + 1 + 2 = H2.length + 3 by omega, List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hl]; omega)]; rfl
    · simp only [img5]
      rw [show H2.length + 1 + 3 = H2.length + 4 by omega, List.getElem?_set_self (by simp [hl]; omega)]; rfl

end

/-- Tag of `x` equals `T`, as a word `1`/`0`. -/
def tagEq (x : MlS) (T : Nat) : ExpHOL 64 :=
  .cmp .equal (.op .and [.shift .lsr (vv x) (.const 26), .const 31]) (.const (BitVec.ofNat 64 T))

/-- The body for one binder kind `T` (5 or 6). -/
def bpKind (C : Ctx) (T : Nat) : ProgHOL 64 :=
  .ite (.op .and [tagEq pBa T, tagEq pBb T])
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pBa)) (.seq eViewP
    (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lDh (vv pBb)) (.seq eViewP
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 8])))
    (alloc5 C lW (.const 4) (vv lA1) (vv lA2) (vv lA3) (vv lB) (.return (vv lW))))))))))))
    (.return (.const 0))

def bpBody (C : Ctx) : ProgHOL 64 :=
  prologue gaaLocals (.ite (vv pLm) (bpKind C 5) (bpKind C 6))

section
variable {σ : Type}

def PostBP (C : Ctx) (o : Option (EIdx × EIdx × EIdx × EIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ q, o = some q → ∃ ob, w = cellA C ob ∧
      BlkAt H' ob [Enc.idxW q.1, Enc.idxW q.2.1, Enc.idxW q.2.2.1, Enc.idxW q.2.2.2]

theorem postBP_locals (C : Ctx) : ∀ (a : Option (EIdx × EIdx × EIdx × EIdx)) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostBP C a w s' st → PostBP C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem tagW_01 (h : EIdx) (k : Nat) : tagW h k = 0 ∨ tagW h k = 1 := by
  unfold tagW; split <;> simp

theorem tagW_and (a b : EIdx) (k : Nat) : (tagW a k &&& tagW b k) ≠ 0 ↔ (tagW a k ≠ 0 ∧ tagW b k ≠ 0) := by
  rcases tagW_01 a k with h1 | h1 <;> rcases tagW_01 b k with h2 | h2 <;> simp [h1, h2]

/-- One binder view: the domain and the body of `h` (tag `T`, 5 or 6). -/
theorem viewB_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64}
    {k : EIdx → EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (h : EIdx) (T : Nat)
    (hT : h.tag = 5 ∨ h.tag = 6) (htT : h.tag.toNat = T) (x y : MlS) (hx : x ∈ DG) (hy : y ∈ DG)
    (hxr : x ≠ lRp)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hk : ∀ ty b P, SpecR (Inv C s ((y, Enc.idxW b) :: (x, Enc.idxW ty) :: (lRp, P) ::
      (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 T) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ) [] DG) rest s (k ty b) R) :
    SpecR (Inv C s Γ M DG)
      (.seq eViewP (.seq (.assign .local x (.load .one (.op .add [vv lRp, .const 0])))
        (.seq (.assign .local y (.load .one (.op .add [vv lRp, .const 8]))) rest)))
      s (do match ← viewBind h with | none => failDanglingE | some (ty, b) => k ty b) R := by
  refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h hT s vw hvw)
    hdh hfl hdir (by decide) (fun vw P htg hsh => ?_)
  obtain ⟨ty, b, hpb, hwv⟩ : ∃ ty b, projBind vw = some (ty, b) ∧ encEView vw = [Enc.idxW ty, Enc.idxW b] := by
    cases vw with
    | lam ty b => exact ⟨ty, b, rfl, rfl⟩
    | forallE ty b => exact ⟨ty, b, rfl, rfl⟩
    | _ => simp [ENodeView.tagN] at htg; rcases hT with e | e <;> rw [e] at htg <;> simp at htg
  rw [hpb]; simp only
  have htg' : vw.tagN = T := by rw [htg, htT]
  refine specR_loadI' x _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) hx (by simp [sev]) rfl
    (by rw [hwv]; exact wordsAt_mem0 _ _ _ _) ?_
  refine specR_loadI' y _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) hy (by simp +decide [sev, Ne.symm hxr]) rfl
    (by rw [hwv]; exact wordsAt_mem1 _ _ _ _ _) ?_
  intro t ht
  refine hk ty b P t ⟨ht.sr, fun z w hz => ?_, fun _ _ hm => absurd hm (by simp), ht.decl⟩
  have := ht.env z w
  simp only [hwv, htg', List.length_cons, List.length_nil] at this ⊢
  exact this hz

end

section
variable {σ : Type}

theorem params_noneBP (vals : List (BitVec 64)) (C : Ctx) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ bpParams.zip vals).get x = none := by
  intro x hx
  have hnot : x ∉ bpParams := by
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

theorem bpKind_spec (C : Ctx) (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    (T : Nat) (hT : T = 5 ∨ T = 6) (a b : EIdx)
    (ha : Γ.get pBa = some (Enc.idxW a)) (hb : Γ.get pBb = some (Enc.idxW b))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DG) (bpKind C T) s
      (if (a.tag == UInt32.ofNat T && b.tag == UInt32.ofNat T) = true then (do
        match ← viewBind a with
        | none => failDanglingE
        | some (ty₁, body₁) =>
          match ← viewBind b with
          | none => failDanglingE
          | some (ty₂, body₂) => pure (some (ty₁, body₁, ty₂, body₂))) else pure none)
      (PostBP (ctxH C H)) := by
  unfold bpKind
  have hsev : sev Γ (.op .and [tagEq pBa T, tagEq pBb T]) = some (tagW a T &&& tagW b T) := by
    simp [sev, tagEq, tagW, ha, hb]
  by_cases hab : a.tag = UInt32.ofNat T ∧ b.tag = UInt32.ofNat T
  · have hc : (a.tag == UInt32.ofNat T && b.tag == UInt32.ofNat T) = true := by simp [hab.1, hab.2]
    rw [if_pos hc]
    have hw : (tagW a T &&& tagW b T) ≠ 0 :=
      (tagW_and a b T).mpr ⟨(tagW_iff a T (by omega) (by omega)).mpr hab.1, (tagW_iff b T (by omega) (by omega)).mpr hab.2⟩
    refine specR_ifI _ _ hsev (fun _ => ?_) (fun e => absurd e hw)
    have hT56 : ∀ e : EIdx, e.tag = UInt32.ofNat T → e.tag = 5 ∨ e.tag = 6 := by
      intro e he; rcases hT with rfl | rfl <;> simp [he]
    have htT : ∀ e : EIdx, e.tag = UInt32.ofNat T → e.tag.toNat = T := by
      intro e he; rw [he]; simp; omega
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle] <;> rfl) ?_
    refine specR_assignI lDh (vv pBa) (Enc.idxW a) (by decide) (by simp +decide [ha]) ?_
    refine viewB_spec a T (hT56 a hab.1) (htT a hab.1) lA1 lA2 (by decide) (by decide) (by decide)
      (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [hdir] <;> rfl) (fun ty₁ body₁ P1 => ?_)
    refine specR_assignI lDh (vv pBb) (Enc.idxW b) (by decide) (by simp +decide [hb]) ?_
    refine viewB_spec b T (hT56 b hab.2) (htT b hab.2) lA3 lB (by decide) (by decide) (by decide)
      (by simp +decide) (by simp +decide <;> rfl) (by simp +decide [hdir] <;> rfl) (fun ty₂ body₂ P2 => ?_)
    refine specR_alloc5I (C := ctxH C H) (ctxOK_H hok H) lW (.const 4) (vv lA1) (vv lA2) (vv lA3) (vv lB) 4
      (Enc.idxW ty₁) (Enc.idxW body₁) (Enc.idxW ty₂) (Enc.idxW body₂) (by decide) (fun _ => rfl)
      (fun _ => by simp +decide) (fun _ => by simp +decide) (fun _ => by simp +decide) (fun _ => by simp +decide)
      (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    exact ⟨_, hp2.trans (img5_prefix H2 ws _ _ _ _ _ hws), sr_of_eq ht.sr rfl rfl rfl rfl, fun e => by simp at e,
      fun q e => by
        simp only [Option.some.injEq] at e; subst e
        exact ⟨H2.length, rfl, img5_blk H2 ws _ _ _ _ hws⟩⟩
  · have hc : (a.tag == UInt32.ofNat T && b.tag == UInt32.ofNat T) = false := by
      by_cases h1 : a.tag = UInt32.ofNat T <;> simp_all
    rw [if_neg (by simp [hc])]
    have hw : (tagW a T &&& tagW b T) = 0 := by
      rcases tagW_01 a T with h1 | h1 <;> rcases tagW_01 b T with h2 | h2
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · exact absurd ⟨(tagW_iff a T (by omega) (by omega)).mp (by simp [h1]),
          (tagW_iff b T (by omega) (by omega)).mp (by simp [h2])⟩ hab
    refine specR_ifI _ _ hsev (fun e => absurd hw e) (fun _ => ?_)
    exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun _ => rfl, fun _ e => by simp at e⟩)

end

section
variable {σ : Type}

theorem bp_spec (C : Ctx) (hok : CtxOK C) (H : List (BitVec 64)) (s : AState) (lam : Bool) (a b : EIdx) :
    SpecR (Pre (σ := σ) (ctxH C H) s (bpParams.zip [if lam then 1 else 0, Enc.idxW a, Enc.idxW b])) (bpBody C) s
      (binderPair? lam a b) (PostBP (ctxH C H)) := by
  refine specR_prologue (postBP_locals _) (params_noneBP _ _) ?_
  unfold binderPair?
  cases lam
  · refine specR_ifI _ 0 (by simp +decide [ctxEnv, bpParams]) (fun h => absurd rfl h) (fun _ => ?_)
    exact bpKind_spec C hok 6 (Or.inr rfl) a b (by simp +decide [ctxEnv, bpParams])
      (by simp +decide [ctxEnv, bpParams]) (by simp +decide [ctxEnv] <;> rfl) (by simp +decide [ctxEnv] <;> rfl)
  · refine specR_ifI _ 1 (by simp +decide [ctxEnv, bpParams]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact bpKind_spec C hok 5 (Or.inl rfl) a b (by simp +decide [ctxEnv, bpParams])
      (by simp +decide [ctxEnv, bpParams]) (by simp +decide [ctxEnv] <;> rfl) (by simp +decide [ctxEnv] <;> rfl)

end

end ConPanqueque.T.ExBP
