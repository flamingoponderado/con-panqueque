import ConPanqueque.Front.InitProg

/-! # The program's parse is con-ron's `parseBytes`

After the pins, `parseBytes b` is `StateD.init` (a probe, `stInit s`), then the lines.  So when
`feedAll (stInit s) b 0 0` succeeds, `parseBytes b` succeeds with the same declarations at the same
final state. -/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge

namespace ConPanqueque.Front

theorem parseBytes_of_feedAll {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    (hp : PinsOK s) {b : ByteArray} (hsz : b.size < USize.size) {st' : StateD}
    (h : feedAll (stInit s) b 0 0 s = .ok (st', s')) :
    parseBytes b s = .ok (.ok (.ofState st'), s') := by
  have ht := feedAll_tail b _ 0 (stInit s) 0 s s' st' rfl h
  unfold tailRun at ht
  obtain ⟨x, s1, hfc, hrest⟩ := AM.bind_ok ht
  rw [parseBytes, if_neg (by omega)]
  rw [bind_ok_apply (show (pure PUnit.unit : AM PUnit) s = .ok (PUnit.unit, s) from rfl)]
  simp only
  rw [bind_ok_apply (stateD_init_probe hok hoff hp)]
  rw [bind_ok_apply hfc]
  cases x with
  | error e => exact absurd (AM.pure_ok hrest).1 (by simp)
  | ok p =>
    obtain ⟨st1, ln, tail⟩ := p
    simp only at hrest ⊢
    by_cases htl : tail < b.usize
    · rw [if_pos htl] at hrest ⊢
      rw [bind_ok_apply hrest]; rfl
    · rw [if_neg htl] at hrest ⊢
      obtain ⟨h1, rfl⟩ := AM.pure_ok hrest
      simp only [Except.ok.injEq] at h1; subst h1; rfl

end ConPanqueque.Front
