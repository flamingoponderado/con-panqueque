import ConPanqueque.V.EGen
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The shared remainder, for any store

`rRest k w fsrc`: the scratch flag through the pointer in `fsrc`, kind `k`'s
descriptors, the key pointer and length, and `internTwo`. `rRest_spec`
concludes any predicate `Q` that holds once kind `k`'s two tables are
represented anew and everything else (other tables, descriptors, flags)
is as before.
-/

namespace ConPanqueque.V

def rRest (k w : Nat) (fsrc : MlS) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv fsrc))
  (.seq (.assign .local lOn (.load .one (vv lFl)))
  (.seq (.assign .local lPg (descK k 0))
  (.seq (.assign .local lSg (descK k 1))
  (.seq (.assign .local lK (vv lKb))
  (.seq (.assign .local lL (.const (BitVec.ofNat 64 w)))
    internTwo)))))

section
variable {σ : Type} {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

theorem rRest_spec (t u : PanSemStateFiniteExact 64 σ) (L : Layout) (FLn FLl FLs FLe KB FL : BitVec 64) (w k : Nat)
    (fsrc : MlS) (hfsrc : fsrc ∉ [lFl, lOn, lPg, lSg, lK, lL])
    (on : Bool) (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64) (hwd : ι → BitVec 64)
    (hinj : ∀ x y, enc x = enc y → x = y) (mkP mkS : Nat → ι) (icap : Nat)
    (hmkP : ∀ i, i < icap → hwd (mkP i) = L.base k 0 + BitVec.ofNat 64 i)
    (hmkS : ∀ i, i < icap → hwd (mkS i) = L.base k 1 + BitVec.ofNat 64 i)
    (hicap : ∀ tier, tier < 2 → (L.geo k tier).cap ≤ icap)
    (P Sc : Tbl α ι δ) (sk : Bool) (x : α) (d : δ)
    (Q : PanSemStateFiniteExact 64 σ → Prop)
    (hQ : ∀ v' : PanSemStateFiniteExact 64 σ, TabAt v' L k 0 enc dW (twoTier P Sc on sk x d mkP mkS).1 mkP →
      TabAt v' L k 1 enc dW (twoTier P Sc on sk x d mkP mkS).2.1 mkS →
      (∀ F, (F = FLn ∨ F = FLl ∨ F = FLs ∨ F = FLe) → v'.memory F = u.memory F) → v'.memaddrs = u.memaddrs →
      (∀ k' tier, k' < 19 → tier < 2 → k' ≠ k → Agree L FLe u v' k' tier) → Q v')
    (hS : SepK L FLn FLl FLs FLe KB w k) (hk19 : k < 19) (hwl : (enc x).length = w) (hw : w < 2 ^ 61)
    (hFL : FL = FLn ∨ FL = FLl ∨ FL = FLs ∨ FL = FLe)
    (hflm : u.memaddrs FL ∧ u.memory FL = .word (if on then 1 else 0))
    (hPa : TabAt u L k 0 enc dW P mkP) (hSa : TabAt u L k 1 enc dW Sc mkS) (hK : Words u KB (enc x))
    (ldv : u.locals.lookup lDv = some (.val (.word (dW d).1)))
    (ldv2 : u.locals.lookup lDv2 = some (.val (.word (dW d).2)))
    (lsk : u.locals.lookup lSk = some (.val (.word (if sk then 1 else 0))))
    (lfs : u.locals.lookup fsrc = some (.val (.word FL)))
    (ldir : u.locals.lookup lDir = some (.val (.word L.DIR))) (lkb : u.locals.lookup lKb = some (.val (.word KB)))
    (hw5 : ∀ y, y ∈ [lFl, lOn, lPg, lSg, lK, lL] → ∃ w, u.locals.lookup y = some (.val (.word w))) :
    Stop (evaluateHOLFiniteState u (rRest k w fsrc)).1 ∨
      ((evaluateHOLFiniteState u (rRest k w fsrc)).1 =
          some (.returned (.val (.word (hwd (twoTier P Sc on sk x d mkP mkS).2.2)))) ∧
        Q (evaluateHOLFiniteState u (rRest k w fsrc)).2 ∧
        (evaluateHOLFiniteState u (rRest k w fsrc)).2.code = u.code ∧
        (evaluateHOLFiniteState u (rRest k w fsrc)).2.globals = u.globals ∧
        (evaluateHOLFiniteState u (rRest k w fsrc)).2.memaddrs = u.memaddrs ∧
        (evaluateHOLFiniteState u (rRest k w fsrc)).2.topAddr = u.topAddr ∧
        ∀ c, ¬ inR (L.geo k 0) c → ¬ inR (L.geo k 1) c → (evaluateHOLFiniteState u (rRest k w fsrc)).2.memory c = u.memory c) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hfsrc
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hfsrc
  have W : ∀ y, y ∈ [lFl, lOn, lPg, lSg, lK, lL] → ∃ w, u.locals.lookup y = some (.val (.word w)) := hw5
  unfold rRest
  obtain ⟨wf, hwf⟩ := W lFl (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u lFl _ FL wf (eval_vv u fsrc _ lfs) hwf)]
  let u1 := setVarHOLFinite lFl (.val (.word FL)) u
  have hld : @evalHOLExact 64 σ _ u1.toExact (fun x => Classical.propDecidable (u1.memaddrs x)) (.load .one (vv lFl)) =
      some (.val (.word (if on then 1 else 0))) := by
    rw [eval_load_word u1 _ _ (eval_vv u1 lFl _ (lookup_setVar_same _ _ _)) hflm.1]
    show some (ValueHOL.val (u.memory FL)) = _; rw [hflm.2]
  obtain ⟨wo, hwo⟩ := W lOn (by decide)
  rw [seq_normal _ (ConsLoop.assign_local u1 lOn _ _ wo hld (by lk [u1]; exact hwo))]
  let u2 := setVarHOLFinite lOn (.val (.word (if on then 1 else 0))) u1
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
  have T := tail_spec u6 L k enc dW hwd mkP mkS icap hmkP hmkS hinj hicap P Sc on sk x d KB
    (tabAt_eq hPa rfl rfl) (tabAt_eq hSa rfl rfl) hS.pow hS.dis
    (fun tier m ht hm => ⟨(hS.dsc k tier m hk19 ht hm).1, (hS.dsc k tier m hk19 ht hm).2.1⟩)
    hK (by rw [hwl]; exact hw) (fun i hi => ⟨hS.kbo i k 0 (by omega) hk19 (by decide), hS.kbo i k 1 (by omega) hk19 (by decide)⟩)
    ⟨by lk [u6, u5], by lk [u6]; try rw [hwl], by lk [u6, u5, u4, u3, u2, u1]; exact ldv,
      by lk [u6, u5, u4, u3, u2, u1]; exact ldv2⟩
    (by lk [u6, u5, u4, u3]) (by lk [u6, u5, u4]) (by lk [u6, u5, u4, u3, u2]) (by lk [u6, u5, u4, u3, u2, u1]; exact lsk)
  rcases T with hs | ⟨hr, hP', hS', c3, g3, d3, ta3, fr3⟩
  · exact Or.inl hs
  refine Or.inr ⟨hr, hQ _ hP' hS' (fun F hF => fr3 F (hS.fls F hF).1 (hS.fls F hF).2.1) d3
    (fun k' tier h1 h2 h4 => ⟨fun m hm => fr3 _ (hS.dsc k' tier m h1 h2 hm).1 (hS.dsc k' tier m h1 h2 hm).2.1,
      fun c hc => fr3 c (hS.oth k' tier c h1 h2 h4 hc).1 (hS.oth k' tier c h1 h2 h4 hc).2⟩),
    c3, g3, d3, ta3, fr3⟩

end

end ConPanqueque.V
