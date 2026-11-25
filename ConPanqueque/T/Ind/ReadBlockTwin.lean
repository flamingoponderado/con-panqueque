import ConPanqueque.T.Ind.Members
import ConPanqueque.T.Ind.ResultSort
import ConPanqueque.T.Ind.Large
import ConPanqueque.T.Ind.Anon

/-!
# `readBlock`, flattened

Past the split (the records are the types, then the constructors, then the recursors), `readBlock` is the
member counts, three level-parameter checks, then `rbTail`: the result sort and flag, the block's own
universe arguments, the groups, the recursor shapes, the members and the elimination parameter.  Lean
elaborates `readBlock`'s `s ← match …` by copying the rest into each branch; `rb_twin` folds it back.
-/

open ConRon.Arena
namespace ConPanqueque.T.Ind

/-- `readBlock` after its checks. -/
def rbTail (nPd k : Nat) (c0 : IConstantVal) (cvTs : List IConstantVal) (ctors : List (IConstantVal × Nat))
    (rsl : List (IConstantVal × Nat × Nat × Bool × List IRecRule)) (r0lps : List NIdx) (nIdxs : List Nat) :
    AM BlockShape := do
  let s ← resSortT (nPd + nIdxs.headD 0) c0.type
  let isProp ← isPropT s
  let lvls ← paramLevels c0.levelParams
  let groups ← blockGroups (cvTs.map (·.name)) lvls nPd k ctors
  let recsL ← rsl.mapM (recShapeOf (cvTs.map (·.name)))
  let members : List MemberShape := ((cvTs.zip nIdxs).zip groups).map fun a => ⟨a.1.1, a.1.1, a.1.2, a.2⟩
  match largeT c0.levelParams r0lps with
  | some elim => pure ⟨members, recsL, nPd, elim, s, true, isProp⟩
  | none => do
    let anon ← internNNode .anonymous
    pure ⟨members, recsL, nPd, anon, s, false, isProp⟩

theorem unwrapE_pure {α : Type} (a : α) : unwrapE (pure (.ok a) : AM (Except CheckError α)) = pure a := by
  simp [unwrapE]

theorem unwrapE_err {α : Type} (e : CheckError) : unwrapE (pure (.error e) : AM (Except CheckError α)) = fail e := by
  simp [unwrapE]

set_option maxHeartbeats 2000000 in
theorem rb_twin (nPd : Nat) (blk : List IConstantInfo) (k nC : Nat) (hle : k + nC ≤ blk.length)
    (h3 : ∀ i, i < k → kindAt blk i = some 3) (h3n : kindAt blk k ≠ some 3)
    (h4 : ∀ i, i < nC → kindAt blk (k + i) = some 4) (h4n : kindAt blk (k + nC) ≠ some 4)
    (h5 : ∀ i, k + nC ≤ i → i < blk.length → kindAt blk i = some 5)
    (c0 : IConstantVal) (cs : List IConstantVal) (hc : (blk.take k).map (·.toConstantVal) = c0 :: cs)
    (r0 : IConstantVal × Nat × Nat × Bool × List IRecRule) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (hrs : ((blk.drop k).drop nC).map recT = r0 :: rs) :
    unwrapE (readBlock nPd blk) = (do
      let nIdxs ← unwrapE (blockMemberCounts nPd (c0 :: cs).length (((blk.drop k).take nC).map ctorT).length
        ((c0 :: cs).map (·.name)) (r0 :: rs) 0 (c0 :: cs))
      if (!(c0 :: cs).all fun c => c.levelParams == c0.levelParams) = true then
        fail (CheckError.invalid "inductive type declares other universe parameters than the block's first type")
      else if (!(((blk.drop k).take nC).map ctorT).all fun c => c.2.1 == nPd) = true then
        fail (CheckError.invalid "constructor declares another parameter count than the block")
      else if (!(((blk.drop k).take nC).map ctorT).all fun c => c.1.levelParams == c0.levelParams) = true then
        if ((c0 :: cs).length == 1) = true then
          fail (CheckError.invalid "constructor declares other universe parameters than its type")
        else
          fail (CheckError.invalid "constructor declares other universe parameters than the block's inductive types")
      else rbTail nPd (c0 :: cs).length c0 (c0 :: cs) ((((blk.drop k).take nC).map ctorT).map (fun c => (c.1, c.2.2))) (r0 :: rs) r0.1.levelParams nIdxs) := by
  rw [readBlock, blockSplit_runs blk k nC hle h3 h3n h4 h4n h5, hc, hrs]
  simp only []
  rw [unwrapE_bind]
  simp only [unwrapE, bind_assoc]
  congr 1; funext r
  cases r with
  | error e => simp [fail_bind']
  | ok nIdxs =>
    simp only [pure_bind]
    split
    · simp [unwrapE_err]
    split
    · simp
    split
    · split <;> simp
    simp only [rbTail, resSortT, isPropT, bind_assoc]
    have hopt : ∀ (eq : Option Bool), (match eq with
        | some true => true
        | some false => false
        | none => false) = optTrue eq := fun eq => by rcases eq with _ | _ | _ <;> rfl
    congr 1; funext x
    cases x with
    | none =>
      simp only [bind_assoc, pure_bind, recShapeOf]
      congr 1; funext y; congr 1; funext z; congr 1; funext eq; congr 1; funext lvls; congr 1; funext groups
      congr 1; funext recsL
      split
      next _ elim heq =>
        rw [show largeT c0.levelParams r0.1.levelParams = some elim from heq]; simp only [unwrapE, pure_bind]
        rcases eq with _ | _ | _ <;> rfl
      next _ heq =>
        rw [show largeT c0.levelParams r0.1.levelParams = none from heq]; simp only [unwrapE, pure_bind, bind_assoc]
        rcases eq with _ | _ | _ <;> rfl
    | some q =>
      simp only [bind_assoc]
      congr 1; funext v
      cases v
      all_goals
        simp only [bind_assoc, pure_bind, recShapeOf]
        congr 1; funext y; congr 1; funext z; congr 1; funext eq; congr 1; funext lvls; congr 1; funext groups
        congr 1; funext recsL
        split
        next _ elim heq =>
          rw [show largeT c0.levelParams r0.1.levelParams = some elim from heq]; simp only [unwrapE, pure_bind]
          rcases eq with _ | _ | _ <;> rfl
        next _ heq =>
          rw [show largeT c0.levelParams r0.1.levelParams = none from heq]; simp only [unwrapE, pure_bind, bind_assoc]
          rcases eq with _ | _ | _ <;> rfl

end ConPanqueque.T.Ind
