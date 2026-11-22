import ConPanqueque.V.ESort
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The shared remainder of every expression intern

A constructor's intern is a prefix (its key in the buffer, its derived value,
its scratch bit) followed by `eRest k w`: the scratch flag, kind `k`'s two
descriptors, the key pointer and length, and `internTwo`. `eRest_spec`: from a
state the prefix leaves, the result is the store's `intern` with all four
stores re-represented — given the store equation and the expression store's
update at kind `k`.
-/

namespace ConPanqueque.V

def eRest (k w : Nat) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lOn (.load .one (vv lFl)))
  (.seq (.assign .local lPg (descK k 0))
  (.seq (.assign .local lSg (descK k 1))
  (.seq (.assign .local lK (vv lKb))
  (.seq (.assign .local lL (.const (BitVec.ofNat 64 w)))
    internTwo)))))

theorem persist_iff {k : IdxKind} (i : Idx k) : i.isPersistent = true ↔ Enc.idxW i >>> (31 : Nat) = 0 := by
  have hw : (Enc.idxW i).toNat = i.word.toNat := by simp [Enc.idxW]
  have e1 : (Enc.idxW i >>> (31 : Nat) = 0) ↔ i.word.toNat / 2147483648 = 0 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow] at this; simpa using this
    · intro h; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow]; simpa using h
  rw [e1]
  simp only [Idx.isPersistent, Idx.tier, beq_iff_eq]
  constructor
  · intro h; have := congrArg UInt32.toNat h; simpa [UInt32.toNat_div] using this
  · intro h; apply UInt32.toNat_inj.mp; simpa [UInt32.toNat_div] using h

/-- The scratch-child bit of a two-child node, as Pancake computes it. -/
theorem eval_sk2 {σ : Type} {k1 k2 : IdxKind} (s : PanSemStateFiniteExact 64 σ) (x y : MlS) (a : Idx k1) (b : Idx k2)
    (ha : s.locals.lookup x = some (.val (.word (Enc.idxW a))))
    (hb : s.locals.lookup y = some (.val (.word (Enc.idxW b)))) :
    @evalHOLExact 64 σ _ s.toExact (fun c => Classical.propDecidable (s.memaddrs c))
      (.cmp .notEqual (.op .or [.shift .lsr (vv x) (.const 31), .shift .lsr (vv y) (.const 31)]) (.const 0)) =
      some (.val (.word (if (if a.isPersistent then !b.isPersistent else true) then 1 else 0))) := by
  rw [ConsLoop.eval_cmp_of s .notEqual _ _ _ 0 (eval_or2 s _ _ _ _ (eval_shr s _ _ _ (eval_vv s x _ ha) (by decide))
    (eval_shr s _ _ _ (eval_vv s y _ hb) (by decide))) (eval_const s 0)]
  simp only [show (31 : BitVec 64).toNat = 31 from rfl]
  have ea := persist_iff a; have eb := persist_iff b
  by_cases pa : a.isPersistent = true <;> by_cases pb : b.isPersistent = true
  · have h0 : (Enc.idxW a >>> (31 : Nat) ||| Enc.idxW b >>> (31 : Nat)) = 0 := by rw [ea.mp pa, eb.mp pb]; rfl
    have hb' : ((Enc.idxW a >>> (31 : Nat) ||| Enc.idxW b >>> (31 : Nat)) == 0) = true := beq_iff_eq.mpr h0
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb', pa, pb, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  all_goals
    have h0 : ¬ (Enc.idxW a >>> (31 : Nat) ||| Enc.idxW b >>> (31 : Nat)) = 0 := fun e => by
      rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff] at e
      first | exact pa (ea.mpr e.1) | exact pb (eb.mpr e.2)
    have hb' : ((Enc.idxW a >>> (31 : Nat) ||| Enc.idxW b >>> (31 : Nat)) == 0) = false := by simpa using h0
    simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hb', Bool.not_false, ↓reduceIte]
    simp_all

section
variable {σ : Type} {α : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

/-- What an intern guarantees, for a node view `v`. -/
def ERes (t : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w : Nat) (st : EStore)
    (res : EStore × EIdx) (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Stop r.1 ∨ (r.1 = some (.returned (.val (.word (Enc.idxW res.2)))) ∧
    SRep r.2 L FLn FLl FLs FLe res.1 ∧ r.2.code = t.code ∧ r.2.globals = t.globals ∧
    r.2.memaddrs = t.memaddrs ∧ r.2.topAddr = t.topAddr ∧
    ∀ c, ¬ inAny L c → (∀ j, j < w → c ≠ KB + BitVec.ofNat 64 (8 * j)) → r.2.memory c = t.memory c)

theorem eRest_spec (t u : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB : BitVec 64) (w k : Nat)
    (st : EStore) (enc : α → List (BitVec 64)) (hinj : ∀ x y, enc x = enc y → x = y)
    (mkP mkS : Nat → EIdx) (icap : Nat)
    (hmkP : ∀ i, i < icap → Enc.idxW (mkP i) = L.base k 0 + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → Enc.idxW (mkS i) = L.base k 1 + BitVec.ofNat 64 i)
    (hicap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ icap)
    (P Sc : Tbl α EIdx UInt64) (sk : Bool) (x : α) (d : UInt64) (res : EStore × EIdx)
    (setK : Tbl α EIdx UInt64 → Tbl α EIdx UInt64 → EStore)
    (hres : res = (setK (twoTier P Sc st.scratchOn sk x d mkP mkS).1 (twoTier P Sc st.scratchOn sk x d mkP mkS).2.1,
      (twoTier P Sc st.scratchOn sk x d mkP mkS).2.2))
    (hlss : ∀ P' S', (setK P' S').lss = st.lss)
    (hset : ∀ (v v' : PanSemStateFiniteExact 64 σ) P' S', ERep v L FLe st → TabAt v' L k 0 enc dWN P' mkP →
      TabAt v' L k 1 enc dWN S' mkS → v'.memory FLe = v.memory FLe → v'.memaddrs = v.memaddrs →
      (∀ k' tier, 9 ≤ k' → k' < 19 → tier < 2 → k' ≠ k → Agree L FLe v v' k' tier) → ERep v' L FLe (setK P' S'))
    (hS : SepK L FLn FLl FLs FLe KB w k) (hk : 9 ≤ k) (hk19 : k < 19) (hwl : (enc x).length = w) (hw : w < 2 ^ 61)
    -- the prefix's end state
    (hR : SRep u L FLn FLl FLs FLe st)
    (hPa : TabAt u L k 0 enc dWN P mkP) (hSa : TabAt u L k 1 enc dWN Sc mkS)
    (hK : Words u KB (enc x))
    (hm : ∀ c, (∀ j, j < w → c ≠ KB + BitVec.ofNat 64 (8 * j)) → u.memory c = t.memory c)
    (hd : u.memaddrs = t.memaddrs) (hc : u.code = t.code) (hg : u.globals = t.globals) (hta : u.topAddr = t.topAddr)
    (ldv : u.locals.lookup lDv = some (.val (.word (dWN d).1)))
    (ldv2 : u.locals.lookup lDv2 = some (.val (.word (dWN d).2)))
    (lsk : u.locals.lookup lSk = some (.val (.word (if sk then 1 else 0))))
    (lfle : u.locals.lookup lFle = some (.val (.word FLe)))
    (ldir : u.locals.lookup lDir = some (.val (.word L.DIR))) (lkb : u.locals.lookup lKb = some (.val (.word KB)))
    (hw5 : ∀ y, y ∈ [lFl, lOn, lPg, lSg, lK, lL] → ∃ w, u.locals.lookup y = some (.val (.word w))) :
    ERes t L FLn FLl FLs FLe KB w st res (evaluateHOLFiniteState u (eRest k w)) := by
  have W : ∀ y, y ∈ [lFl, lOn, lPg, lSg, lK, lL] → ∃ w, u.locals.lookup y = some (.val (.word w)) := hw5
  unfold eRest
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u lFl _ FLe wf (eval_vv u lFle _ lfle) hwf)]
  let u1 := setVarHOLFinite lFl (.val (.word FLe)) u
  have hld : @evalHOLExact 64 σ _ u1.toExact (fun x => Classical.propDecidable (u1.memaddrs x)) (.load .one (vv lFl)) =
      some (.val (.word (if st.scratchOn then 1 else 0))) := by
    rw [eval_load_word u1 _ _ (eval_vv u1 lFl _ (lookup_setVar_same _ _ _)) hR.e.fl.1]
    show some (ValueHOL.val (u.memory FLe)) = _; rw [hR.e.fl.2]
  obtain ⟨wo, hwo⟩ := W lOn (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u1 lOn _ _ wo hld (by lk [u1]; exact hwo))]
  let u2 := setVarHOLFinite lOn (.val (.word (if st.scratchOn then 1 else 0))) u1
  have dir2 : u2.locals.lookup lDir = some (.val (.word L.DIR)) := by lk [u2, u1]; exact ldir
  obtain ⟨wp, hwp⟩ := W lPg (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u2 lPg (descK k 0) (descAddr L k 0) wp
    (by unfold descK; exact eval_add2 u2 _ _ _ _ (eval_vv u2 lDir _ dir2) (eval_const u2 _)) (by lk [u2, u1]; exact hwp))]
  let u3 := setVarHOLFinite lPg (.val (.word (descAddr L k 0))) u2
  obtain ⟨wg, hwg⟩ := W lSg (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u3 lSg (descK k 1) (descAddr L k 1) wg
    (by unfold descK; exact eval_add2 u3 _ _ _ _ (eval_vv u3 lDir _ (by lk [u3]; exact dir2)) (eval_const u3 _))
    (by lk [u3, u2, u1]; exact hwg))]
  let u4 := setVarHOLFinite lSg (.val (.word (descAddr L k 1))) u3
  obtain ⟨wk, hwk⟩ := W lK (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u4 lK _ KB wk (eval_vv u4 lKb _ (by lk [u4, u3, u2, u1]; exact lkb))
    (by lk [u4, u3, u2, u1]; exact hwk))]
  let u5 := setVarHOLFinite lK (.val (.word KB)) u4
  obtain ⟨wl, hwl'⟩ := W lL (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u5 lL _ (BitVec.ofNat 64 w) wl (eval_const u5 _) (by lk [u5, u4, u3, u2, u1]; exact hwl'))]
  let u6 := setVarHOLFinite lL (.val (.word (BitVec.ofNat 64 w))) u5
  have T := tail_spec u6 L k enc dWN Enc.idxW mkP mkS icap hmkP hmkS hinj hicap P Sc st.scratchOn sk x d KB
    (tabAt_eq hPa rfl rfl) (tabAt_eq hSa rfl rfl) hS.pow hS.dis (fun tier m ht hm => ⟨(hS.dsc k tier m hk19 ht hm).1, (hS.dsc k tier m hk19 ht hm).2.1⟩)
    hK (by rw [hwl]; exact hw) (fun i hi => ⟨hS.kbo i k 0 (by omega) hk19 (by decide), hS.kbo i k 1 (by omega) hk19 (by decide)⟩)
    ⟨by lk [u6, u5], by lk [u6]; try rw [hwl], by lk [u6, u5, u4, u3, u2, u1]; exact ldv,
      by lk [u6, u5, u4, u3, u2, u1]; exact ldv2⟩
    (by lk [u6, u5, u4, u3]) (by lk [u6, u5, u4]) (by lk [u6, u5, u4, u3, u2]) (by lk [u6, u5, u4, u3, u2, u1]; exact lsk)
  rcases T with hs | ⟨hr, hP', hS', c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  have agO : ∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → Agree L FLe u (evaluateHOLFiniteState u6 internTwo).2 k' tier :=
    fun k' tier h1 h2 h4 => ⟨fun m hm => fr3 _ (hS.dsc k' tier m h1 h2 hm).1 (hS.dsc k' tier m h1 h2 hm).2.1,
      fun c hc => fr3 c (hS.oth k' tier c h1 h2 h4 hc).1 (hS.oth k' tier c h1 h2 h4 hc).2⟩
  have flF : ∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) →
      (evaluateHOLFiniteState u6 internTwo).2.memory F = u.memory F := fun F hF =>
    fr3 F (hS.fls F hF).1 (hS.fls F hF).2.1
  rw [hres]
  refine Or.inr ⟨hr, ?_, c3.trans hc, g3.trans hg, d3.trans hd, ta3.trans hta, fun c h1 h2 => ?_⟩
  · refine low_frame hR ⟨flF _ (Or.inl rfl), flF _ (Or.inr (Or.inl rfl)), flF _ (Or.inr (Or.inr (Or.inl rfl)))⟩ d3
      (fun k' tier h1 h2 => agO k' tier (by omega) h2 (by omega)) _ (hlss _ _) ?_
    exact hset u _ _ _ hR.e hP' hS' (flF _ (Or.inr (Or.inr (Or.inr rfl)))) d3 (fun k' tier _ h2 h3 h4 => agO k' tier h2 h3 h4)
  · have n0 : ¬ inR (L.geo k 0) c := fun hc => h1 ⟨k, 0, hk19, by decide, hc⟩
    have n1 : ¬ inR (L.geo k 1) c := fun hc => h1 ⟨k, 1, hk19, by decide, hc⟩
    rw [fr3 c n0 n1]; exact hm c h2

end

end ConPanqueque.V
