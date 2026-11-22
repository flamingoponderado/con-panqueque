import ConPanqueque.Hash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Hash

/-- `mixHash he ke` as one Pancake expression. -/
def mixExp (he ke : ExpHOL 64) : ExpHOL 64 :=
  let km : ExpHOL 64 := .panop .mul [ke, M]
  .panop .mul [.op .xor [he, .op .xor [.op .xor [km, .shift .lsr km (.const 47)], M]], M]

theorem eval_mixExp {σ : Type} (s : PanSemStateFiniteExact 64 σ) (he ke : ExpHOL 64) (a b : UInt64)
    (ha : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) he =
      some (.val (.word a.toBitVec)))
    (hb : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) ke =
      some (.val (.word b.toBitVec))) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (mixExp he ke) =
      some (.val (.word (leanMixHash a b).toBitVec)) := by
  simp [mixExp, evalHOLExact, evalListHOLExact, ha, hb, M, wordOpHOL, wordOp, valueIsWord, valueWord,
    panOpHOL, wordShiftHOL, leanMixHash]
