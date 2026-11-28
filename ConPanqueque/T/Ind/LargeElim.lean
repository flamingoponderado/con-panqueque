import ConPanqueque.T.Ind.RecPins

/-!
# The large-elimination guard (`blockLargeElimAllowed`, an unnested block)

The block's sort never zero (`nz`, the never-zero walk), or one member with at most one constructor; otherwise
the port hangs (the twin rejects). The member count `k` is a parameter (any `k`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

theorem nz_isNeverZero : ∀ l : ConLeche.Level, nz l = ConLeche.Level.isNeverZero l
  | .zero => rfl
  | .succ _ => rfl
  | .param _ => rfl
  | .max a b => by simp [nz, ConLeche.Level.isNeverZero, nz_isNeverZero a, nz_isNeverZero b]
  | .imax _ b => by simp [nz, ConLeche.Level.isNeverZero, nz_isNeverZero b]

def leaS := ofString "lea_s"
def leaN := ofString "lea_n"
def leaX := ofString "lea_x"
def leaK := ofString "lea_k"
def fLea := ofString "largeElimGuard"

def leaParams : List MlS := [leaS, leaN, leaK]
def leaLocals : List MlS := [leaX]

def leaBody : ProgHOL 64 := prologue leaLocals
  (.seq (.call (some (some (.local, leaX), none)) fNz0 [vv leaS])
  (.ite (.cmp .equal (vv leaX) (.const 0))
    (.ite (.cmp .equal (vv leaK) (.const 1))
      (.ite (.cmp .lower (vv leaN) (.const 2)) (.return (.const 0)) hang)
      hang)
    (.return (.const 0))))

section
variable {σ : Type}

theorem lea_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ leaLocals → (ctxEnv C ++ leaParams.zip vals).get x = none :=
  Knot.params_none C leaLocals leaParams vals (by decide) (by decide)

/-- **The guard** on a large unnested block of any member count, its sort denoting at the floor. -/
theorem lea_spec (C : Ctx) (hcz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one))
    (p : BlockShape) (hlg : p.large = true) (hkb : p.k < 2 ^ 63) (lsr : ConLeche.Level)
    (hSd : denoteL C.St.ls p.resSort = some lsr) (hnc : p.numCtors < 2 ^ 63) (X : CheckError) (s : AState) :
    SpecR (σ := σ) (Pre C s (leaParams.zip [Enc.idxW p.resSort, BitVec.ofNat 64 p.numCtors, BitVec.ofNat 64 p.k])) leaBody s
      (blockLargeElimAllowed p false >>= fun b => if b then pure () else fail X) (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals _) (lea_none _ _) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  have hwf := sr_lwf ht0.sr
  have hrl := ht0.sr.cok.rl
  have hl : denoteL s.store.ls p.resSort = some lsr := denoteL_ext hSd ht0.sr.floor
  obtain ⟨Xc, hx, hX⟩ := readLevelM_runC p.resSort s lsr hrl hl
  simp only [blockLargeElimAllowed, bind_assoc]
  refine specR_quiet hx rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (fun hc => cachesOK_readLC hc Xc hX) ?_
  rw [← nz_isNeverZero]
  refine specR_congr (m' := (pure (nz lsr) : AM Bool) >>= fun z =>
    (if z = true then pure true else if false = true then pure false
      else pure (p.large && p.k == 1 && (p.numCtors == 0 || p.numCtors == 1))) >>= fun b =>
      if b = true then pure () else fail X) (by simp only [pure_bind]) ?_
  refine specR_callNIH (C := ctxH C C.H) leaX fNz0 [nzU] [vv leaS] nzBody [Enc.idxW p.resSort]
    (by decide) rfl (by decide) hcz ⟨by simp +decide [sev, Env.get, leaParams, ctxEnv], trivial⟩
    (PostBS (ctxH C C.H) _) (fun a w s' _ => w = boolW a)
    (fun a w s' st ⟨h1, h2, h3⟩ => ⟨C.H, List.prefix_refl _, h2, by subst h1; exact h3⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [nzU] _ rfl hlk)
      (nz0_spec (ctxH C C.H) hcz { s with caches := { s.caches with readLC := Xc } } hwf lsr p.resSort hl))
    (fun b w s4 H4 hp4 hw => ?_)
  subst hw
  have hp4' : C.H <+: H4 := hp4
  cases b
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases hk' : ¬ p.k = 1
    · have hk := hk'
      have hne : BitVec.ofNat 64 p.k ≠ 1#64 := fun e => hk (by
        have := congrArg BitVec.toNat e; simp at this; omega)
      exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, leaParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => specR_hangI)
    have hk : p.k = 1 := Decidable.of_not_not hk'
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, leaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk]) (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases hn : p.numCtors < 2
    · have hlw := ConPanqueque.T.Decl.nd_lt_iff p.numCtors 2 (by omega) (by omega)
      refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, leaParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hn]) (fun _ => ?_) (fun h => absurd h (by decide))
      have hok : (p.large && p.k == 1 && (p.numCtors == 0 || p.numCtors == 1)) = true := by
        simp [hlg, hk]; omega
      simp only [Bool.false_eq_true, ↓reduceIte, hok, pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hp4', sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hlw := ConPanqueque.T.Decl.nd_lt_iff p.numCtors 2 (by omega) (by omega)
      exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, leaParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h)
        (fun _ => specR_hangI)
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte, pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hp4', sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
