import ConPanqueque.Front.ParseTop
import ConPanqueque.T.Decl.FoldVerdict
import ConPanqueque.Front.IndRun

/-! # The registry is the fold's record block

`FrontSt`'s registry (`DeclsRel`) gives the fold's input: a block of record addresses (`BlkAt` at
the registry cell) with every record in the `RecOK` layout, once each declaration denotes. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.T.Decl

theorem denoteNList_get {ns : NStore} : ∀ {hs : List NIdx} {ks : List ConLeche.Name},
    denoteNList ns hs = some ks → ∃ hkl : ks.length = hs.length,
      ∀ j (hj : j < hs.length), denoteN ns hs[j] = some (ks[j]'(by omega))
  | [], ks, h => by simp [denoteNList] at h; subst h; exact ⟨rfl, fun j hj => by simp at hj⟩
  | x :: xs, ks, h => by
    simp only [denoteNList] at h
    split at h
    · rename_i y ys h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl, hg⟩ := denoteNList_get h2
      refine ⟨by simp [hl], fun j hj => ?_⟩
      cases j with
      | zero => simpa using h1
      | succ j => simpa using hg j (by simpa using hj)
    · simp at h

theorem recCV_of_enc {C : Ctx} {F : Nat} {H : List (BitVec 64)} {q : Nat} {cv : IConstantVal}
    (h : CVEnc C F H q cv) (hd : (denoteCV C.St cv).isSome) : RecCV (ctxH C H) q cv := by
  obtain ⟨ol, -, h1, h2, h3, h4, h5⟩ := h
  unfold denoteCV at hd
  split at hd
  · rename_i n lps ty hn hl hty
    obtain ⟨hkl, hg⟩ := denoteNList_get hl
    exact ⟨ol, lps, h1, h2, h3, h4, h5, hkl, hg, by show (denoteE C.St cv.type).isSome = true; rw [hty]; rfl⟩
  · simp at hd

theorem recOK_of_enc {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration}
    (h : RecEnc C F H o d) (hd : (denoteDecl C.St d).isSome) : RecOK (ctxH C H) o d := by
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
    simp only [denoteDecl] at hd
    split at hd
    · rename_i c x hc hx
      exact ⟨h1, recCV_of_enc h2 (by rw [hc]; rfl), h3, h4, h5, by show (denoteE C.St v).isSome = true; rw [hx]; rfl⟩
    · simp at hd
  | thmDecl cv v =>
    obtain ⟨-, h1, h2, h3⟩ := h
    simp only [denoteDecl] at hd
    split at hd
    · rename_i c x hc hx; exact ⟨h1, recCV_of_enc h2 (by rw [hc]; rfl), h3⟩
    · simp at hd
  | opaqueDecl cv v =>
    obtain ⟨-, h1, h2, h3⟩ := h
    simp only [denoteDecl] at hd
    split at hd
    · rename_i c x hc hx; exact ⟨h1, recCV_of_enc h2 (by rw [hc]; rfl), h3⟩
    · simp at hd
  | axiomDecl cv =>
    obtain ⟨-, h1, h2, h3, -⟩ := h
    simp only [denoteDecl] at hd
    cases hc : denoteCV C.St cv with
    | none => rw [hc] at hd; simp at hd
    | some c => exact ⟨h1, recCV_of_enc h2 (by rw [hc]; rfl), h3⟩
  | quotDecl k cv =>
    obtain ⟨-, h1, h2, h3⟩ := h
    simp only [denoteDecl] at hd
    cases hc : denoteCV C.St cv with
    | none => rw [hc] at hd; simp at hd
    | some c =>
      refine ⟨h1, recCV_of_enc h2 (by rw [hc]; rfl), ?_⟩
      show H[o + 4]? = _
      rw [h3]; cases k <;> rfl
  | indDecl block nP =>
    -- not yet a front record: the dispatcher rejects inductive lines.  Once it accepts them, `IndSem.run` is
    -- `indRun_of_front` (Front/IndRun.lean) of the line's `IndShape`/`IndBounds` (as `IndFront`) and `IndRunGap`.
    exact absurd h.1 (by simp [ConPanqueque.Bridge.IsFrontDecl, ConPanqueque.Bridge.IsValueDecl])

/-- **The registry as the fold's block.** -/
theorem registry_block {C : Ctx} {F rb capD : Nat} {H : List (BitVec 64)} {decls : Array IDeclaration}
    (h : DeclsRel C F rb capD H decls) (hd : ∀ k (hk : k < decls.size), (denoteDecl C.St decls[k]).isSome) :
    ∃ rs : List (Nat × IDeclaration), rs.map Prod.snd = decls.toList ∧
      BlkAt H rb (rs.map (fun r => cellA C r.1)) ∧ ∀ j (hj : j < rs.length), RecOK (ctxH C H) rs[j].1 rs[j].2 := by
  obtain ⟨h1, -, -, -, h5⟩ := h
  let o : Fin decls.size → Nat := fun k => Classical.choose (h5 k.1 k.2)
  have ho : ∀ k : Fin decls.size, H[rb + 1 + k.1]? = some (cellA C (o k)) ∧ RecEnc C F H (o k) decls[k.1] :=
    fun k => Classical.choose_spec (h5 k.1 k.2)
  refine ⟨List.ofFn (fun k => (o k, decls[k.1])), ?_, ⟨?_, fun i hi => ?_⟩, fun j hj => ?_⟩
  · apply List.ext_getElem (by simp) (fun i h1 h2 => by simp)
  · simpa using h1
  · simp only [List.length_map, List.length_ofFn] at hi
    simpa using (ho ⟨i, hi⟩).1
  · simp only [List.length_ofFn] at hj
    simp only [List.getElem_ofFn]
    exact recOK_of_enc (ho ⟨j, hj⟩).2 (hd j hj)

end ConPanqueque.Front
