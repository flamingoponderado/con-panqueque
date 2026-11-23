import ConPanqueque.T.MemoClear
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The `EIdx → Nat` memos in a caller

`bvarBGet`/`fvarBGet` and their setters: the key is the one word `idxW h` in `KB[0]`, the value
word is `ofNat n` (every stored value below `2^63`).
-/

namespace ConPanqueque.T

variable {σ : Type}

theorem encN_inj : ∀ x y, encN x = encN y → x = y := by
  intro x y h
  simp only [encN, List.cons.injEq, and_true] at h
  exact Enc.idxW_inj h

theorem natW_add_one_ne (n : Nat) (hn : n < 2 ^ 63) : natW n + 1 ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp [natW, BitVec.toNat_add] at this
  omega

/-- The post-condition may assume the twin's run. -/
theorem specR_run {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR P c s m R) :
    SpecR P c s m (fun a w s' t => m s = .ok (a, s') ∧ R a w s' t) := by
  intro t ht
  rcases h t ht with hs | ⟨w, hn, a, s', hm, hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hn, a, s', hm, hm, hr⟩

theorem specR_memoGetNI {β : Type} {C : Ctx} (mk : MemoNK) (getOp : EIdx → AM (Option Nat))
    (hget : ∀ key s, getOp key s = .ok ((memoSelN mk s.memos)[key]?, s))
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Option Nat → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eh : ExpHOL 64) (h : EIdx) (hx : x ∈ D)
    (heh : sev Γ eh = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ r, (∀ n, r = some n → n < 2 ^ 63) → SpecR (Inv C s ((x, optWG natW r) :: Γ) [] D) rest s (k r) R) :
    SpecR (Inv C s Γ M D)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eh)
        (.seq (.call (some (some (.local, x), none)) fMemoGet [.const (C.mG (.n mk)), .const 1]) rest))
      s (getOp h >>= k) R := by
  refine specR_storeKBI hok 0 (by decide) eh (Enc.idxW h) heh hkb ?_
  refine specR_call2IM x fMemoGet pG pLen (by decide) (.const (C.mG (.n mk))) (.const 1) memoGetBody (C.mG (.n mk))
    1 hx hcodeG rfl rfl
    (fun a w s' st => s' = s ∧ w = optWG natW a ∧ (∀ n, a = some n → n < 2 ^ 63) ∧ SR C s st)
    (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2.2.2)
    (fun u hsr hM h1 h2 => ?_) (fun a w s' st hp => by obtain ⟨rfl, rfl, hb, _⟩ := hp; exact hk a hb)
  have hW : Words u C.KB (encN h) := by
    intro j hj
    have e : j = 0 := by simp [encN] at hj; omega
    subst e; exact hM _ _ (by simp [encN])
  have G := memoGet_spec (σ := σ) (α := Unit) (C.mG (.n mk)) C.KB (C.mg (.n mk)) encN_inj (memoSelN mk s.memos) h s u
    (hsr.memoN mk).1 hW (by simp [encN]) hsr.gkb h1 h2 (by rw [hsr.code]; exact hcodeP)
  refine specR_congr (hget h s) (specR_mono (specR_run G) (fun v hv => hv) (fun a w s' st hp => ?_))
  obtain ⟨hrun, hs, hw, hm, hd', hg, hc⟩ := hp
  have ha : a = (memoSelN mk s.memos)[h]? := by
    simp only [pure, StateT.pure, Except.pure] at hrun; cases hrun; rfl
  exact ⟨hs, hw, fun n hn => (hsr.memoN mk).2 h n (ha ▸ hn), sr_of_eq hsr hm hd' hg hc⟩

theorem specR_memoSetNI {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoNK) (setOp : EIdx → Nat → AM Unit)
    (hset : ∀ key r s, setOp key r s =
      .ok ((), { s with memos := memoUpdN mk s.memos ((memoSelN mk s.memos).insert key r) }))
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eh ev : ExpHOL 64) (h : EIdx) (r : Nat) (hr : r < 2 ^ 63) (hx : x ∈ D)
    (heh : sev Γ eh = some (Enc.idxW h)) (hev : sev Γ ev = some (natW r)) (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w, SpecR (Inv C { s with memos := memoUpdN mk s.memos ((memoSelN mk s.memos).insert h r) }
      ((x, w) :: Γ) [] D) rest { s with memos := memoUpdN mk s.memos ((memoSelN mk s.memos).insert h r) }
      (k ()) R) :
    SpecR (Inv C s Γ M D)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) eh)
        (.seq (.call (some (some (.local, x), none)) fMemoSet [.const (C.mG (.n mk)), .const 1, ev]) rest))
      s (setOp h r >>= k) R := by
  let s' : AState := { s with memos := memoUpdN mk s.memos ((memoSelN mk s.memos).insert h r) }
  refine specR_storeKBI hok 0 (by decide) eh (Enc.idxW h) heh hkb ?_
  refine specR_call3IM x fMemoSet pG pLen pVal (by decide) (by decide) (by decide) (.const (C.mG (.n mk))) (.const 1) ev
    memoSetBody (C.mG (.n mk)) 1 (natW r) hx hcodeS rfl rfl hev
    (fun _ _ s'' st => s'' = s' ∧ SR C s' st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2)
    (fun u hsr hM h1 h2 h3 => ?_) (fun a w s'' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk w)
  have hW : Words u C.KB (encN h) := by
    intro j hj
    have e : j = 0 := by simp [encN] at hj; omega
    subst e; exact hM _ _ (by simp [encN])
  have S := memoSet_spec (σ := σ) (C.mG (.n mk)) C.KB (C.mg (.n mk)) encN_inj (memoSelN mk s.memos) h r s u
    (hsr.memoN mk).1 hW (by simp [encN])
    (fun j hj => hok.kbMemo (.n mk) j (by simp [encN] at hj; omega)) (fun j hj => hok.mdescMemo (.n mk) (.n mk) j hj)
    hsr.gkb h1 h2 h3 (by rw [hsr.code]; exact hcodeI)
  intro t ht
  rcases S t ht with hs | ⟨w, hr', _, s'', _, hp⟩
  · exact Or.inl hs
  obtain ⟨_, hmem, hfr, hd', hg, hc⟩ := hp
  subst ht
  refine Or.inr ⟨w, hr', (), s', hset h r s, rfl, ⟨srep_frame hsr.rep ⟨hfr _ (hok.flMemo (.n mk) _ (Or.inl rfl)),
      hfr _ (hok.flMemo (.n mk) _ (Or.inr (Or.inl rfl))),
      hfr _ (hok.flMemo (.n mk) _ (Or.inr (Or.inr (Or.inl rfl)))), hfr _ (hok.flMemo (.n mk) _ (Or.inr (Or.inr (Or.inr rfl))))⟩ hd'
      (fun kk tier hk1 hk2 => ⟨fun mm hm => hfr _ (hok.dirMemo (.n mk) kk tier mm hk1 hk2 hm),
        fun c hc => hfr c (fun hin => hok.memoOut (.n mk) c hin ⟨kk, tier, hk1, hk2, hc⟩)⟩),
    by rw [hg]; exact hsr.gdir, by rw [hg]; exact hsr.gfln, by rw [hg]; exact hsr.gfll, by rw [hg]; exact hsr.gfls,
    by rw [hg]; exact hsr.gfle, by rw [hg]; exact hsr.gkb, by rw [hc]; exact hsr.code,
    fun j hj => by rw [hd']; exact hsr.kbuf j hj, fun mk' => ?_, fun nk => ?_,
    fun ck => cacheAt_frame (hsr.cache ck) (fun c hc => hfr c (hok.memoDis (.c ck) (.n mk) c (by simp) hc))
      (fun kk hkk => hfr _ (hok.mdescMemo (.n mk) (.c ck) kk hkk)) hd',
    heapEx_frame hsr.heap (fun i hi => hfr _ (hok.heapMemo (.n mk) i hi)) hd' (by rw [hg])⟩⟩
  · show MemoAt _ _ _ (memoSel mk' (memoUpdN mk s.memos _)); rw [memoSel_updN]
    exact memoAt_frame (hsr.memo mk') (fun c hc => hfr c (hok.memoDis (.e mk') (.n mk) c (by simp) hc))
      (fun kk hkk => hfr _ (hok.mdescMemo (.n mk) (.e mk') kk hkk)) hd'
  by_cases e : nk = mk
  · subst e; show MemoAtN _ _ _ (memoSelN nk (memoUpdN nk s.memos _)); rw [memoSelN_upd_same]
    refine ⟨hmem, fun k' v hv => ?_⟩
    rw [Std.HashMap.getElem?_insert] at hv
    split at hv
    · cases hv; exact hr
    · exact (hsr.memoN nk).2 k' v hv
  · show MemoAtN _ _ _ (memoSelN nk (memoUpdN mk s.memos _)); rw [memoSelN_upd_ne mk nk e]
    exact memoAtN_frame (hsr.memoN nk) (fun c hc => hfr c (hok.memoDis (.n nk) (.n mk) c (fun x => e (by cases x; rfl)) hc))
      (fun kk hkk => hfr _ (hok.mdescMemo (.n mk) (.n nk) kk hkk)) hd'

end ConPanqueque.T
