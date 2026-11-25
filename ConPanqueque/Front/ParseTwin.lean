import ConPanqueque.Front.InitProg
import ConRon.Bridge.Frontend.Chunks

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
  rw [parseBytes, ite_eq_right (by omega)]
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
    · rw [ite_eq_left htl] at hrest ⊢
      rw [bind_ok_apply hrest]; rfl
    · rw [ite_eq_right htl] at hrest ⊢
      obtain ⟨h1, rfl⟩ := AM.pure_ok hrest
      simp only [Except.ok.injEq] at h1; subst h1; rfl

theorem denoteDecls_isSome {st : EStore} : ∀ {ds : List IDeclaration} {xs : List ConLeche.Declaration},
    denoteDecls st ds = some xs → ∀ d ∈ ds, (denoteDecl st d).isSome
  | [], _, _, d, hd => by simp at hd
  | d0 :: ds, xs, h, d, hd => by
    simp only [denoteDecls] at h
    split at h
    · rename_i x xs' h1 h2
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [h1]; rfl
      · exact denoteDecls_isSome h2 d hd
    · simp at h

/-- What the program's parse gives on the twin side. -/
theorem parse_twin {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    (hp : PinsOK s) {b : ByteArray} (hsz : b.size < USize.size) {st' : StateD}
    (h : feedAll (stInit s) b 0 0 s = .ok (st', s')) :
    ConRon.Bridge.Frontend.ParseStep s s' ∧ ConRon.Bridge.Frontend.PersParseResult (.ofState st') ∧
      ∃ rc, ConLeche.Frontend.parseBytes b = .ok rc ∧ denoteDecls s'.store st'.decls.toList = some rc.decls.toList := by
  obtain ⟨h1, h2, rc, h3, h4⟩ := ConRon.Bridge.Frontend.parseBytes_run hok hoff hp (parseBytes_of_feedAll hok hoff hp hsz h)
  refine ⟨h1, h2, rc, h3, ?_⟩
  exact ConRon.Bridge.Frontend.denoteDeclArray_iff.mp h4.decls

end ConPanqueque.Front
