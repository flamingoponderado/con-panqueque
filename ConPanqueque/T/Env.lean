import ConPanqueque.T.MemoG
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Reading the environment

`fe.find? n`: the constant table's read at key `[idxW n]` gives `0` for a miss and `p + 1` for the
constant's block at `p`; the block's fields are loads from the environment heap.
-/

namespace ConPanqueque.T

theorem encNI_inj : ∀ x y, encNI x = encNI y → x = y := by
  intro x y h
  simp only [encNI, List.cons.injEq, and_true] at h
  exact Enc.idxW_inj h

theorem ecell_add (C : Ctx) (o i : Nat) : ecell C o + BitVec.ofNat 64 (8 * i) = ecell C (o + i) := by
  unfold ecell
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem ecell_succ_ne {C : Ctx} (hok : CtxOK C) {o : Nat} (ho : o < C.EN) : ecell C o + 1 ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  have hl := hok.envLay
  simp only [ecell, BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  rw [Nat.mod_eq_of_lt (show 8 * o < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show C.EB.toNat + 8 * o < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show C.EB.toNat + 8 * o + 1 < 2 ^ 64 by omega)] at this
  simp at this

theorem ecell_succ_sub (C : Ctx) (o : Nat) : ecell C o + 1 - 1 = ecell C o := by
  rw [BitVec.add_sub_cancel]

/-- The block of `n`'s constant: the table's answer, as the continuation receives it. -/
theorem find_rel {C : Ctx} (hok : CtxOK C) (n : NIdx) :
    match C.fe.find? n with
    | none => C.envM[n]? = none
    | some ci => ∃ o, C.envM[n]? = some (ecell C o) ∧ CIE C.EB C.EH o ci := hok.envRel.1 n

theorem cie_lt {EB : BitVec 64} {H : List (BitVec 64)} {o : Nat} {ci : IConstantInfo} (h : CIE EB H o ci) :
    o < H.length := by
  have h0 : ∃ w, H[o]? = some w := by
    obtain ⟨_, h2⟩ := h
    cases ci <;> simp only at h2
    all_goals first
      | exact ⟨_, h2⟩
      | exact ⟨_, h2.1⟩
  obtain ⟨w, hw⟩ := h0
  exact (List.getElem?_eq_some_iff.mp hw).1

section
variable {σ : Type}

/-- `KB[0] := en; x := memoGet(constant table, 1); rest`: the twin's `fe.find? n` (pure). -/
def envFindP (C : Ctx) (x : MlS) (en : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) en)
    (.seq (.call (some (some (.local, x), none)) fMemoGet [.const (C.mG .env), .const 1]) rest)

theorem specR_envFindI {β : Type} {C : Ctx} (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (en : ExpHOL 64) (n : NIdx) (hx : x ∈ D) (hen : sev Γ en = some (Enc.idxW n))
    (hkb : Γ.get lKb = some C.KB)
    (hk : SpecR (Inv C s ((x, optWG id C.envM[n]?) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (envFindP C x en rest) s m R := by
  refine specR_storeKBI hok 0 (by decide) en (Enc.idxW n) hen hkb ?_
  refine specR_congr (m' := (pure C.envM[n]? : AM (Option (BitVec 64))) >>= fun _ => m) rfl ?_
  exact specR_memoGetGI (K := NIdx) (V := BitVec 64) encNI_inj (C.mG .env) (C.mg .env) C.envM n _ rfl
    (fun u hu => hu.env.2.1) hcodeG hcodeP x (.const (C.mG .env)) (.const 1) hx rfl rfl (by simp [encNI])
    (fun u hM j hj => by
      have e : j = 0 := by simp [encNI] at hj; omega
      subst e; exact hM _ (Enc.idxW n) (by simp)) hk

/-- `x := load e` at environment-heap cell `j`. -/
theorem specR_envLoadI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (j : Nat) (w : BitVec 64)
    (hx : x ∈ D) (he : sev Γ e = some (ecell C j)) (hw : C.EH[j]? = some w)
    (h : SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one e)) rest) s m R := by
  obtain ⟨hj, hjw⟩ := List.getElem?_eq_some_iff.mp hw
  refine specR_pre_assign x (.load .one e) (fun _ => w) (fun t ht => ?_) (fun t ht => ht.decl x hx)
    (fun t ht => inv_set ht x w) h
  have hE := ht.sr.env.1
  rw [EV, eval_load_word t _ _ (inv_ev ht he) (hE.dom j (Nat.lt_of_lt_of_le hj hE.len))]
  have := hE.val j hj
  unfold ecell
  rw [this, hjw]

end

end ConPanqueque.T
