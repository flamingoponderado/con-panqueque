import ConPanqueque.T.Ind.ReadBlock
import ConPanqueque.T.Ind.RecPins
import ConRon.Bridge.Pers

/-! # `readBlock`'s split, at a one-member block

`readBlock_splitOK`: an accepting run of the twin's `readBlock` whose answer has one member satisfies
`SplitOK`: the split is `blockSplit`'s, its formers one per member, its recursor records one per recursor,
its constructors the members' (one group, all of them). -/

open ConRon.Arena

namespace ConPanqueque.T.Ind

set_option autoImplicit false

theorem pure_ok_eq {α : Type} {a b : α} {s s' : AState} (h : (pure a : AM α) s = .ok (b, s')) : a = b ∧ s = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h

set_option maxHeartbeats 2000000 in
theorem rb_twin' (nPd : Nat) (blk : List IConstantInfo) (c0 : IConstantVal) (cs : List IConstantVal)
    (cs3 : List (IConstantVal × Nat × Nat))
    (r0 : IConstantVal × Nat × Nat × Bool × List IRecRule) (rs : List (IConstantVal × Nat × Nat × Bool × List IRecRule))
    (hsp : blockSplit blk = some (c0 :: cs, cs3, r0 :: rs)) :
    unwrapE (readBlock nPd blk) = (do
      let nIdxs ← unwrapE (blockMemberCounts nPd (c0 :: cs).length cs3.length
        ((c0 :: cs).map (·.name)) (r0 :: rs) 0 (c0 :: cs))
      if (!(c0 :: cs).all fun c => c.levelParams == c0.levelParams) = true then
        fail (CheckError.invalid "inductive type declares other universe parameters than the block's first type")
      else if (!cs3.all fun c => c.2.1 == nPd) = true then
        fail (CheckError.invalid "constructor declares another parameter count than the block")
      else if (!cs3.all fun c => c.1.levelParams == c0.levelParams) = true then
        if ((c0 :: cs).length == 1) = true then
          fail (CheckError.invalid "constructor declares other universe parameters than its type")
        else
          fail (CheckError.invalid "constructor declares other universe parameters than the block's inductive types")
      else rbTail nPd (c0 :: cs).length c0 (c0 :: cs) (cs3.map (fun c => (c.1, c.2.2))) (r0 :: rs) r0.1.levelParams nIdxs) := by
  rw [readBlock, hsp]
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


theorem unwrapE_of_ok {α : Type} {x : AM (Except CheckError α)} {s s' : AState} {a : α}
    (h : x s = .ok (.ok a, s')) : unwrapE x s = .ok (a, s') := by
  simp only [unwrapE, bind, StateT.bind, h]; rfl

theorem blockGroups_out {names : List NIdx} {lvls : LsIdx} {nP k : Nat} {cs : List (IConstantVal × Nat)}
    {s s' : AState} {g : List (List (IConstantVal × Nat))} (h : blockGroups names lvls nP k cs s = .ok (g, s')) :
    (k = 1 → g = [cs]) ∧ g.length = k := by
  unfold blockGroups at h
  by_cases hk : k = 1
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte] at h
    obtain ⟨rfl, -⟩ := pure_ok_eq h
    exact ⟨fun _ => rfl, rfl⟩
  · rw [if_neg (by simpa using hk)] at h
    refine ⟨fun e => absurd e hk, ?_⟩
    have := mapM_len _ _ _ _ _ h
    simpa using this

theorem readBlock_splitOK {nPd : Nat} {block : List IConstantInfo} {s s' : AState} {p : BlockShape}
    (h : readBlock nPd block s = .ok (.ok p, s')) (hm : p.members.length = 1) : SplitOK p block := by
  have hu := unwrapE_of_ok h
  -- the split
  have hspl : ∃ c0 cs cs3 r0 rs, blockSplit block = some (c0 :: cs, cs3, r0 :: rs) := by
    unfold readBlock at h
    cases hsp : blockSplit block with
    | none => simp only [hsp] at h; obtain ⟨e, -⟩ := pure_ok_eq h; cases e
    | some q =>
    obtain ⟨cvTs, cs, rs⟩ := q
    simp only [hsp] at h
    cases cvTs with
    | nil => obtain ⟨e, -⟩ := pure_ok_eq h; cases e
    | cons c0 cs' =>
    cases rs with
    | nil => obtain ⟨e, -⟩ := pure_ok_eq h; cases e
    | cons r0 rs' => exact ⟨c0, cs', cs, r0, rs', rfl⟩
  obtain ⟨c0, cs, cs3, r0, rs, hsp⟩ := hspl
  rw [rb_twin' nPd block c0 cs cs3 r0 rs hsp] at hu
  obtain ⟨nIdxs, s1, h1, h2⟩ := bind_ok_inv' hu
  have hnl := bmc_length _ _ _ _ _ _ _ _ _ _ h1
  split at h2
  · exact absurd h2 (fun hc => ConRon.Bridge.AM.fail_ok hc)
  split at h2
  · exact absurd h2 (fun hc => ConRon.Bridge.AM.fail_ok hc)
  split at h2
  · split at h2 <;> exact absurd h2 (fun hc => ConRon.Bridge.AM.fail_ok hc)
  unfold rbTail at h2
  obtain ⟨_, s2, -, h3⟩ := bind_ok_inv' h2
  obtain ⟨_, s3, -, h4⟩ := bind_ok_inv' h3
  obtain ⟨_, s4, -, h5⟩ := bind_ok_inv' h4
  obtain ⟨groups, s5, hg, h6⟩ := bind_ok_inv' h5
  obtain ⟨recsL, s6, hr, h7⟩ := bind_ok_inv' h6
  have hrl := mapM_len _ _ _ _ _ hr
  obtain ⟨hg1, hgl⟩ := blockGroups_out hg
  have hp : p.members = (((c0 :: cs).zip nIdxs).zip groups).map (fun a => (⟨a.1.1, a.1.1, a.1.2, a.2⟩ : MemberShape)) ∧
      p.recs = recsL := by
    split at h7
    · obtain ⟨rfl, -⟩ := pure_ok_eq h7; exact ⟨rfl, rfl⟩
    · obtain ⟨_, s7, -, h8⟩ := bind_ok_inv' h7
      obtain ⟨rfl, -⟩ := pure_ok_eq h8; exact ⟨rfl, rfl⟩
  obtain ⟨hpm, hpr⟩ := hp
  have hk : (c0 :: cs).length = 1 := by
    have := congrArg List.length hpm
    simp only [List.length_map, List.length_zip, hnl, hgl] at this
    omega
  have hg' := hg1 hk
  subst hg'
  refine ⟨c0 :: cs, cs3, r0 :: rs, hsp, ?_, by rw [hpr, hrl], ?_⟩
  · show _ = p.members.length; rw [hm]; exact hk
  · obtain ⟨cs0, rfl⟩ : cs = [] := by simpa using hk
    rw [List.length_singleton] at hnl
    obtain ⟨n0, rfl⟩ : ∃ n0, nIdxs = [n0] := by
      match nIdxs, hnl with
      | [n0], _ => exact ⟨n0, rfl⟩
    simp [BlockShape.allCtors, hpm]

end ConPanqueque.T.Ind
