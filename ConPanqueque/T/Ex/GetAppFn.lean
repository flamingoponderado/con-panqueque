import ConPanqueque.T.Store
import ConRon.Arena.ExprOps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# A first translated function: `getAppFn`

The twin's `getAppFn` (the head of an application spine, by fuel):

    | 0, _ => fail …
    | fuel + 1, h => do
      if h.tag == ETag.app then
        match ← viewApp h with
        | none => failDanglingE
        | some (f, _) => getAppFn fuel f
      else pure h

as a Pancake function `getAppFn(fu, h0)`, refined by hand with the `Spec` combinators: the template
the translator automates.
-/

namespace ConPanqueque.T.Ex

def fGetAppFn := ofString "getAppFn"
def pFu := ofString "fu"
def pH := ofString "h0"
def lX := ofString "x"

/-- Nonzero iff the handle word's tag is `app`: bit 30 (wide), or the narrow tag field 4. -/
def isAppE (e : ExpHOL 64) : ExpHOL 64 :=
  .op .or [.op .and [.shift .lsr e (.const 30), .const 1],
    .cmp .equal (.op .and [.shift .lsr e (.const 26), .const 31]) (.const 4)]

def isAppW (w : BitVec 64) : BitVec 64 := ((w >>> (30 : Nat)) &&& 1) ||| bw ((w >>> (26 : Nat)) &&& 31 = 4)

theorem isApp_iff (h : EIdx) : isAppW (Enc.idxW h) ≠ 0 ↔ h.tag = 4 := by
  have hw : (Enc.idxW h).toNat = h.word.toNat := by simp [Enc.idxW]
  have hlt : h.word.toNat < 2 ^ 32 := h.word.toNat_lt
  have e30 : ((Enc.idxW h >>> (30 : Nat)) &&& 1) = 0 ↔ ¬ (h.word.toNat / 1073741824 % 2 = 1) := by
    constructor
    · intro e c; have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow] at this
      have e1 : (1 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
      rw [e1, Nat.and_two_pow_sub_one_eq_mod] at this; simp at this; omega
    · intro c; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, hw, Nat.shiftRight_eq_div_pow]
      have e1 : (1 : BitVec 64).toNat = 2 ^ 1 - 1 := rfl
      rw [e1, Nat.and_two_pow_sub_one_eq_mod]; simp; omega
  have hwide : h.isWide = true ↔ h.word.toNat / 1073741824 % 2 = 1 := by
    simp only [Idx.isWide, beq_iff_eq]
    constructor
    · intro c; have := congrArg UInt32.toNat c; simpa [UInt32.toNat_div, UInt32.toNat_mod] using this
    · intro c; apply UInt32.toNat_inj.mp; simpa [UInt32.toNat_div, UInt32.toNat_mod] using c
  have hn := narrow_app_iff h
  unfold isAppW
  rw [Ne, show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl, e30]
  by_cases hb : h.word.toNat / 1073741824 % 2 = 1
  · have hw' : h.isWide = true := hwide.mpr hb
    have ht : h.tag = 4 := by simp [Idx.tag, hw']
    simp [hb, ht]
  · have hw' : h.isWide = false := by cases c : h.isWide; rfl; exact absurd (hwide.mp c) hb
    by_cases h4 : (Enc.idxW h >>> (26 : Nat)) &&& 31 = 4
    · have e : bw ((Enc.idxW h >>> (26 : Nat)) &&& 31 = 4) = 1 := if_pos h4
      rw [e]; simp [hb, (hn.mp h4).2]
    · have : ¬ h.tag = 4 := fun c => h4 (hn.mpr ⟨hw', c⟩)
      have e : bw ((Enc.idxW h >>> (26 : Nat)) &&& 31 = 4) = 0 := if_neg h4
      rw [e]; simp [hb, this]

theorem eval_isApp {σ : Type} (t : PanSemStateFiniteExact 64 σ) (x : MlS) (w : BitVec 64)
    (hx : t.locals.lookup x = some (.val (.word w))) : T.EV t (isAppE (vv x)) = some (.val (.word (isAppW w))) := by
  unfold isAppE isAppW T.EV
  rw [eval_or2 t _ _ _ _ (eval_and2' t _ _ _ _ (eval_shr t _ _ _ (eval_vv t x _ hx) (by decide)) (eval_const t 1))
    (ConsLoop.eval_cmp_of t .equal _ _ _ 4 (eval_and2' t _ _ _ _ (eval_shr t _ _ _ (eval_vv t x _ hx) (by decide))
      (eval_const t 31)) (eval_const t 4))]
  simp only [show (30 : BitVec 64).toNat = 30 from rfl, show (26 : BitVec 64).toNat = 26 from rfl]
  by_cases h : (w >>> (26 : Nat)) &&& 31 = 4
  · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [bw, h, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

def getAppFnCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
   (.ite (isAppE (vv pH))
     (.seq (.assign .local lFl (vv lFle))
     (.seq (.assign .local lDh (vv pH))
     (.seq eViewP
     (.seq (.assign .local lX (.load .one (vv lRp)))
     (.seq (.call (some (some (.local, lX), none)) fGetAppFn [.op .sub [vv pFu, .const 1], vv lX])
       (.return (vv lX)))))))
     (.return (vv pH)))

def getAppFnLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, lX]

def getAppFnBody : ProgHOL 64 :=
  .dec lDir .one (.var .global gDir) (.dec lFle .one (.var .global gFle) (decs0 getAppFnLocals getAppFnCore))

section
variable {σ : Type}

def Entry (C : Ctx) (s : AState) (fuel : Nat) (h : EIdx) (u : PState σ) : Prop :=
  SR C s u ∧ u.locals.lookup pFu = some (.val (.word (BitVec.ofNat 64 fuel))) ∧
    u.locals.lookup pH = some (.val (.word (Enc.idxW h)))

def Post (C : Ctx) (s : AState) (a : EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = Enc.idxW a ∧ s' = s ∧ SR C s st

def Inner (C : Ctx) (s : AState) (fuel : Nat) (h : EIdx) (t : PState σ) : Prop :=
  SR C s t ∧ t.locals.lookup pFu = some (.val (.word (BitVec.ofNat 64 fuel))) ∧
    t.locals.lookup pH = some (.val (.word (Enc.idxW h))) ∧ t.locals.lookup lDir = some (.val (.word C.L.DIR)) ∧
    t.locals.lookup lFle = some (.val (.word C.FLe)) ∧
    (∀ x, x ∈ getAppFnLocals → ∃ w, t.locals.lookup x = some (.val (.word w)))

theorem post_locals (C : Ctx) (s : AState) : ∀ (a : EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    Post C s a w s' st → Post C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem body_of_core (C : Ctx) (s : AState) (fuel : Nat) (h : EIdx) (m : AM EIdx)
    (hc : SpecR (Inner (σ := σ) C s fuel h) getAppFnCore s m (Post C s)) :
    SpecR (Entry (σ := σ) C s fuel h) getAppFnBody s m (Post C s) := by
  unfold getAppFnBody
  refine specR_dec lDir (.var .global gDir) _ (fun _ => C.L.DIR) (fun t ht => eval_gv t gDir _ ht.1.gdir)
    (P1 := fun u => ∃ t, Entry C s fuel h t ∧ u = setVarHOLFinite lDir (.val (.word C.L.DIR)) t) ?_
    (fun t ht => ⟨t, ht, rfl⟩) (post_locals C s)
  refine specR_dec lFle (.var .global gFle) _ (fun _ => C.FLe)
    (fun u ⟨t, ht, hu⟩ => eval_gv u gFle _ (by rw [hu]; exact ht.1.gfle))
    (P1 := fun u => ∃ t, (∃ t0, Entry C s fuel h t0 ∧ t = setVarHOLFinite lDir (.val (.word C.L.DIR)) t0) ∧
      u = setVarHOLFinite lFle (.val (.word C.FLe)) t) ?_ (fun t ht => ⟨t, ht, rfl⟩) (post_locals C s)
  refine specR_decs0 (post_locals C s) getAppFnCore (Inner C s fuel h) hc getAppFnLocals _ ?_
  rintro u ⟨t1, ⟨t0, ⟨hsr, hfu, hh⟩, rfl⟩, rfl⟩ t' ⟨m1, d1, g1, c1, fr1, z1⟩
  refine ⟨sr_of_eq hsr m1 d1 g1 c1, ?_, ?_, ?_, ?_, fun x hx => ⟨0, z1 x hx⟩⟩
  · rw [fr1 _ (by decide)]; lk; exact hfu
  · rw [fr1 _ (by decide)]; lk; exact hh
  · rw [fr1 _ (by decide)]; lk
  · rw [fr1 _ (by decide)]; lk

end

section
variable {σ : Type}

theorem ofNat_succ_sub_one (n : Nat) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  rw [← BitVec.ofNat_add_ofNat]; exact BitVec.add_sub_cancel _ _

theorem ofNat_ne_zero (n : Nat) (h0 : n ≠ 0) (h : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

/-- After the view in the `app` arm. -/
def Mid (C : Ctx) (s : AState) (n : Nat) (f a : EIdx) (t : PState σ) : Prop :=
  SR C s t ∧ (∃ P, t.locals.lookup lRp = some (.val (.word P)) ∧ Words t P (Enc.encApp ⟨f, a⟩)) ∧
    t.locals.lookup pFu = some (.val (.word (BitVec.ofNat 64 (n + 1)))) ∧
    (∀ x, x ∈ getAppFnLocals → ∃ w, t.locals.lookup x = some (.val (.word w)))

theorem getAppFn_spec (C : Ctx)
    (hcode : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)) :
    ∀ fuel (h : EIdx) (s : AState), fuel < 2 ^ 64 →
      SpecR (Entry (σ := σ) C s fuel h) getAppFnBody s (getAppFn fuel h) (Post C s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h s _
    apply body_of_core
    refine specR_if (.cmp .equal (vv pFu) (.const 0)) (fun _ => 1) (fun t ht => ?_) specR_hang
      (specR_false fun t ht => absurd ht.2 (by decide))
    unfold T.EV
    rw [ConsLoop.eval_cmp_of t .equal _ _ _ 0 (eval_vv t pFu _ ht.2.1) (eval_const t 0)]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  | succ n ih =>
    intro h s hf
    apply body_of_core
    refine specR_if (.cmp .equal (vv pFu) (.const 0)) (fun _ => 0) (fun t ht => ?_)
      (specR_false fun t ht => ht.2 rfl) ?_
    · unfold T.EV
      rw [ConsLoop.eval_cmp_of t .equal _ _ _ 0 (eval_vv t pFu _ ht.2.1) (eval_const t 0)]
      have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact this
    refine specR_congr (m' := if h.tag == ETag.app then (do
        match ← ConRon.Arena.viewApp h with
        | none => failDanglingE
        | some (f, _) => getAppFn n f) else pure h) (by rw [getAppFn]; rfl) ?_
    refine specR_ite (isAppE (vv pH)) (fun _ => isAppW (Enc.idxW h)) (fun t ht => eval_isApp t pH _ ht.1.2.2.1)
      (fun t _ => by rw [isApp_iff]; simp [ETag.app]) ?_ ?_
    · -- the `app` arm
      by_cases h4' : h.tag ≠ 4
      · exact specR_false fun t ht => h4' (by simpa [ETag.app] using ht.2)
      have h4 : h.tag = 4 := Classical.not_not.mp h4'
      refine specR_pre_assign lFl (vv lFle) (fun _ => C.FLe) (fun t ht => eval_vv t lFle _ ht.1.1.2.2.2.2.1)
        (fun t ht => ht.1.1.2.2.2.2.2 lFl (by decide))
        (P1 := fun t => Inner C s (n + 1) h t ∧ t.locals.lookup lFl = some (.val (.word C.FLe))) (fun t ht => ?_) ?_
      · obtain ⟨⟨⟨hsr, hfu, hh, hdir, hfle, hw⟩, _⟩, _⟩ := ht
        refine ⟨⟨sr_of_eq hsr rfl rfl rfl rfl, by lk; exact hfu, by lk; exact hh, by lk; exact hdir, by lk; exact hfle,
          fun x hx => ?_⟩, by lk⟩
        by_cases e : x = lFl
        · subst e; exact ⟨_, lookup_setVar_same _ _ _⟩
        · obtain ⟨w, hw⟩ := hw x hx; exact ⟨w, by rw [lookup_setVar_other _ _ e]; exact hw⟩
      refine specR_pre_assign lDh (vv pH) (fun _ => Enc.idxW h) (fun t ht => eval_vv t pH _ ht.1.2.2.1)
        (fun t ht => ht.1.2.2.2.2.2 lDh (by decide))
        (P1 := fun t => (Inner C s (n + 1) h t ∧ t.locals.lookup lFl = some (.val (.word C.FLe))) ∧
          t.locals.lookup lDh = some (.val (.word (Enc.idxW h)))) (fun t ht => ?_) ?_
      · obtain ⟨⟨hsr, hfu, hh, hdir, hfle, hw⟩, hfl⟩ := ht
        refine ⟨⟨⟨sr_of_eq hsr rfl rfl rfl rfl, by lk; exact hfu, by lk; exact hh, by lk; exact hdir, by lk; exact hfle,
          fun x hx => ?_⟩, by lk; exact hfl⟩, by lk⟩
        by_cases e : x = lDh
        · subst e; exact ⟨_, lookup_setVar_same _ _ _⟩
        · obtain ⟨w, hw⟩ := hw x hx; exact ⟨w, by rw [lookup_setVar_other _ _ e]; exact hw⟩
      refine specR_bind (Q1 := fun r s' t' => ∃ f a, r = some (f, a) ∧ s' = s ∧ Mid C s n f a t')
        (spec_viewApp (C := C) h h4 (fun t ht => ?_) (fun t ht f a hr => ?_)) ?_
      · obtain ⟨⟨⟨hsr, hfu, hh, hdir, hfle, hw⟩, hfl⟩, hdh⟩ := ht
        exact ⟨hsr, hdh, hdir, hfl, hw lDt (by decide), hw lDg (by decide), hw lDi (by decide), hw lRp (by decide),
          hw lRn (by decide)⟩
      · obtain ⟨⟨⟨hsr, hfu, hh, hdir, hfle, hw⟩, hfl⟩, hdh⟩ := ht
        obtain ⟨_, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, _, hdt, hdg, hdi, hfr⟩ := hr
        refine ⟨f, a, rfl, rfl, sr_of_eq hsr hm hd hg hc, ⟨P, hrp, fun j hj => by rw [hm, hd]; exact hW j hj⟩,
          by rw [hfr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hfu, fun x hx => ?_⟩
        by_cases e1 : x = lRp
        · subst e1; exact ⟨P, hrp⟩
        by_cases e2 : x = lRn
        · subst e2; exact ⟨_, hrn⟩
        by_cases e3 : x = lDt
        · subst e3; exact ⟨_, hdt⟩
        by_cases e4 : x = lDg
        · subst e4; exact ⟨_, hdg⟩
        by_cases e5 : x = lDi
        · subst e5; exact ⟨_, hdi⟩
        obtain ⟨w, hw⟩ := hw x hx; exact ⟨w, by rw [hfr x e1 e2 e3 e4 e5]; exact hw⟩
      intro r s'
      rintro t ⟨f, a, hr, hs', hmid⟩
      subst hr; subst s'
      have hrest : SpecR (Mid (σ := σ) C s n f a) (.seq (.assign .local lX (.load .one (vv lRp)))
          (.seq (.call (some (some (.local, lX), none)) fGetAppFn [.op .sub [vv pFu, .const 1], vv lX])
            (.return (vv lX)))) s (getAppFn n f) (Post C s) := by
        refine specR_pre_assign lX (.load .one (vv lRp)) (fun _ => Enc.idxW f) (fun t ht => ?_)
          (fun t ht => ht.2.2.2 lX (by decide))
          (P1 := fun t => Mid C s n f a t ∧ t.locals.lookup lX = some (.val (.word (Enc.idxW f)))) (fun t ht => ?_) ?_
        · obtain ⟨_, ⟨P, hrp, hW⟩, _⟩ := ht
          obtain ⟨h1, h2⟩ := hW 0 (by simp [Enc.encApp])
          simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h1 h2
          rw [T.EV, eval_load_word t _ _ (eval_vv t lRp _ hrp) h1, h2]; rfl
        · obtain ⟨hsr, ⟨P, hrp, hW⟩, hfu, hw⟩ := ht
          refine ⟨⟨sr_of_eq hsr rfl rfl rfl rfl, ⟨P, by lk; exact hrp, hW⟩, by lk; exact hfu, fun x hx => ?_⟩, by lk⟩
          by_cases e : x = lX
          · subst e; exact ⟨_, lookup_setVar_same _ _ _⟩
          · obtain ⟨w, hw⟩ := hw x hx; exact ⟨w, by rw [lookup_setVar_other _ _ e]; exact hw⟩
        refine specR_congr (m' := getAppFn n f >>= fun a => pure a) (by simp) ?_
        refine specR_bind (Q1 := fun b s' t' => s' = s ∧ SR C s t' ∧
            t'.locals.lookup lX = some (.val (.word (Enc.idxW b))))
          (spec_call2 lX fGetAppFn pFu pH (by decide) (.op .sub [vv pFu, .const 1]) (vv lX) getAppFnBody
            (fun _ => BitVec.ofNat 64 n) (fun _ => Enc.idxW f) (fun t ht => by rw [ht.1.1.code]; exact hcode)
            (fun t ht => by
              rw [T.EV, eval_sub2 t _ _ _ _ (eval_vv t pFu _ ht.1.2.2.1) (eval_const t 1), ofNat_succ_sub_one])
            (fun t ht => eval_vv t lX _ ht.2) (fun t ht => ⟨_, ht.2⟩) (fun _ => Post C s)
            (fun t ht callee h1 h2 u hu => ih f s (by omega) u (by
              subst hu; exact ⟨sr_of_eq ht.1.1 rfl rfl rfl rfl, h1, h2⟩))
            (fun t ht b w s' st hp => ?_)) ?_
        · obtain ⟨hw, hs, hsr⟩ := hp
          refine ⟨hs, sr_of_eq hsr rfl rfl rfl rfl, ?_⟩
          simp only [setKvarHOLFinite]; rw [hw]; exact lookup_setVar_same _ _ _
        intro b s'
        refine specR_return (vv lX) (fun _ => Enc.idxW b) (fun t ht => eval_vv t lX _ ht.2.2) (fun t ht => ?_)
        refine ⟨rfl, ht.1, ?_⟩
        rw [return_state t _ _ (eval_vv t lX _ ht.2.2)]
        exact sr_of_eq ht.2.1 rfl rfl rfl rfl
      exact specR_congr rfl hrest t hmid
    · -- not an `app`
      refine specR_return (vv pH) (fun _ => Enc.idxW h) (fun t ht => eval_vv t pH _ ht.1.1.2.2.1) (fun t ht => ?_)
      refine ⟨rfl, rfl, ?_⟩
      rw [return_state t _ _ (eval_vv t pH _ ht.1.1.2.2.1)]
      exact sr_of_eq ht.1.1.1 rfl rfl rfl rfl

end

end ConPanqueque.T.Ex
