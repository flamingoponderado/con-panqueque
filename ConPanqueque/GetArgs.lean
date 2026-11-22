import ConPanqueque.Spine
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Spine

/-!
# Collecting a spine's arguments into an array

`getArgs(u)`: count the spine's arguments (`spineLen`), allocate that many words
at the heap pointer (stopping if the arena is full), and `fill` them with the
argument pointers. `getArgs_spec`: it returns an array representing con-leche's
`getAppArgs` in the grown arena (`ArgArr`).
-/

namespace ConPanqueque.GetArgs

def iU := ofString "u"
def iN := ofString "n"
def iN8 := ofString "n8"
def iQ := ofString "q"
def iR := ofString "r"

/-- An array of expression pointers at `q` representing `es`. -/
def ArgArr (hh : Heap) (q : BitVec 64) (es : List ConLeche.Expr) : Prop :=
  ∃ ps, All2 (fun p a => ExprAt hh p a) ps es ∧
    ∀ j (hj : j < ps.length), hh (q + BitVec.ofNat 64 (8 * j)) = some (.word ps[j])

theorem all2_mono {hh hh' : Heap} (hs : Sub hh hh') : ∀ {ps : List (BitVec 64)} {es : List ConLeche.Expr},
    All2 (fun p a => ExprAt hh p a) ps es → All2 (fun p a => ExprAt hh' p a) ps es
  | _, _, .nil => .nil
  | _, _, .cons r t => .cons (exprAt_mono hs r) (all2_mono hs t)

def getArgsBody (sl fl : MlS) : ProgHOL 64 :=
  .dec iN .one (.const 0) (.seq (.call (some (some (.local, iN), none)) sl [.var .local iU])
   (.dec iN8 .one (.shift .lsl (.var .local iN) (.const 3))
    (.ite (.cmp .lower (.op .sub [.topAddr, .var .global nHp]) (.var .local iN8)) hang
     (.dec iQ .one (.var .global nHp) (.seq (.assign .global nHp (.op .add [.var .global nHp, .var .local iN8]))
      (.dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) fl
          [.var .local iU, .op .add [.var .local iQ, .var .local iN8]])
        (.return (.var .local iQ)))))))))

theorem getArgs_spec {σ : Type} (sl fl : MlS) (t : PanSemStateFiniteExact 64 σ) (lo hp p : BitVec 64)
    (e : ConLeche.Expr) (hi : AInv t lo hp) (he : ExprAt (hOf t lo hp) p e)
    (hcs : t.code.lookup sl = some ([(Spine.iC, .one)], spineLenBody sl, .one))
    (hcf : t.code.lookup fl = some ([(Spine.iC, .one), (iA, .one)], fillBody fl, .one))
    (hu : t.locals.lookup iU = some (.val (.word p))) (hn : numArgs e < 2 ^ 60)
    (hck : 1 + numArgs e + (1 + numArgs e) ≤ t.clock) :
    RRes t (evaluateHOLFiniteState t (getArgsBody sl fl)) lo hp (fun hh q => ArgArr hh q (args e))
      (1 + numArgs e + (1 + numArgs e)) := by
  have hm := (ainv_arena hi).1
  obtain ⟨ps, hsp, hall⟩ := spArgs_of_exprAt e he
  have hlen : ps.length = numArgs e := by
    have : ∀ {ps : List (BitVec 64)} {es : List ConLeche.Expr}, All2 (fun p a => ExprAt (hOf t lo hp) p a) ps es →
        ps.length = es.length := by
      intro ps es h; induction h with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    rw [this hall, args_length]
  let n := numArgs e
  let n8 := BitVec.ofNat 64 (8 * n)
  have hn8 : n8.toNat = 8 * n := by simp [n8]; omega
  unfold getArgsBody
  apply pure_step sl Spine.iC iN (spineLenBody sl) _ _ n (1 + n) t lo hp p (BitVec.ofNat 64 n) (.var .local iU) hi hcs
    (by simp [evalHOLExact]; rw [lookup_setVar_other _ _ (by decide)]; exact hu) (by omega)
    (fun s' cd mm md g hx hc => by
      obtain ⟨st, ev, post⟩ := spineLen_spec sl (hOf t lo hp) he (by omega) s' (by rw [cd]; exact hcs)
        (fun a w ha => by rw [mm, md]; exact hm a w ha) hx hc
      exact ⟨st, ev, post⟩)
  intro t1 l1n l1o m1 c1 g1 d1 ta1 ck1
  have hai1 : AInv t1 lo hp := ainv_of_eq hi g1 d1 ta1
  let t2 := setVarHOLFinite iN8 (.val (.word n8)) t1
  obtain ⟨L2, e2⟩ := dec_word' t1 iN8 (.shift .lsl (.var .local iN) (.const 3)) n8 _
    (by simp [evalHOLExact, l1n, wordShiftHOL]; apply BitVec.eq_of_toNat_eq
        simp [n8, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega)
  rw [e2]; apply rres_locals'
  have hg2 : t2.globals.lookup nHp = some (.val (.word hp)) := hai1.hpv
  have l2n8 : t2.locals.lookup iN8 = some (.val (.word n8)) := by simp [t2]
  rw [ite_word t2 _ _ _ (if t2.topAddr - hp < n8 then 1 else 0)
    (by simp [evalHOLExact, evalListHOLExact, hg2, l2n8, wordOpHOL, wordOp, valueIsWord, valueWord,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hfull : t2.topAddr - hp < n8
  · simp only [hfull, ↓reduceIte]
    split
    · left; rw [hang_spec _ _ rfl]; exact Or.inl rfl
    · rename_i hh; exact absurd (by decide) hh
  simp only [hfull, ↓reduceIte]
  split
  · rename_i hh; exact absurd rfl hh
  sorry

end ConPanqueque.GetArgs
