import ConPanqueque.Pipeline.IndExt.Base
import ConLeche.Verify.Inductives.BlockInv

/-! # The block's last checks at an extension: the projection tables and the ι reads

`checkBlockTables` reads resolution, storage and the table slot of each structure: all agree at an
extension (`EnvExt`'s table clause).  `blockReadsOk` reads `find?` positively only. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

theorem checkStructProjTable_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) (t : ProjTable)
    (h : checkStructProjTable (m := CheckM) t X₁ = .ok ()) : checkStructProjTable (m := CheckM) t X₂ = .ok () := by
  unfold checkStructProjTable at h ⊢
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h ⊢
  by_cases h1 : t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined t.levelParams && b.constsResolve X₁ && b.looseBVarsBounded (t.numParams + 1))
  · have h1' : t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined t.levelParams && b.constsResolve X₂ && b.looseBVarsBounded (t.numParams + 1)) := by
      refine ⟨h1.1, ?_⟩
      have := h1.2
      rw [Array.all_eq_true] at this ⊢
      intro i hi
      have hb := this i hi
      simp only [Bool.and_eq_true] at hb ⊢
      exact ⟨⟨⟨hb.1.1.1, hb.1.1.2⟩, res_ext hx hb.1.2⟩, hb.2⟩
    rw [if_pos h1] at h; rw [if_pos h1']
    simp only [pure, Except.pure] at h ⊢
    by_cases h2 : (X₁.find? t.structName).isSome = true
    · rw [if_pos h2] at h
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h2
      have h2' : (X₂.find? t.structName).isSome = true := by rw [hx.find _ ci hci]; rfl
      rw [if_pos h2']
      rw [hx.table _ h2]
      exact h
    · rw [if_neg h2] at h; exact nomatch h
  · rw [if_neg h1] at h; exact nomatch h

theorem checkBlockTables_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) :
    ∀ (Q : List ProjTable), checkBlockTables (m := CheckM) X₁ Q = .ok () → checkBlockTables (m := CheckM) X₂ Q = .ok ()
  | [], _ => rfl
  | t :: Q, h => by
    have hall := checkBlockTables_inv h
    unfold checkBlockTables
    rw [checkStructProjTable_ext hx t (hall t (List.mem_cons_self ..))]
    exact checkBlockTables_ext hx Q (by
      unfold checkBlockTables at h
      obtain ⟨u, -, h⟩ := exceptBind_ok h
      exact h)

/-! ## The ι reads, positive in `find?` -/

/-- `g` answers every lookup `f` answers, alike. -/
def Grows (f g : Name → Option ConstantInfo) : Prop := ∀ n ci, f n = some ci → g n = some ci

variable {f g : Name → Option ConstantInfo}

theorem annWitness_mono (hg : Grows f g) (e : Expr) (h : annWitness f e = true) : annWitness g e = true := by
  unfold annWitness at h ⊢
  split at h
  · rename_i n
    split at h
    · rename_i c hc; rw [hg _ _ hc]; exact h
    · exact nomatch h
  · exact nomatch h

theorem annIdentVal_mono (hg : Grows f g) (ps : List Name) (k : Nat) (v : Expr)
    (h : annIdentVal f ps k v = true) : annIdentVal g ps k v = true := by
  unfold annIdentVal at h ⊢
  split at h
  · exact h
  · simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨h.1, h.2.elim Or.inl (fun h' => Or.inr (annWitness_mono hg _ h'))⟩
  · exact nomatch h

theorem annIdent_mono (hg : Grows f g) (n : Name) (k : Nat) (h : annIdent f n k = true) : annIdent g n k = true := by
  unfold annIdent at h ⊢
  split at h
  · rename_i cv v hint hf; rw [hg _ _ hf]; exact annIdentVal_mono hg _ _ _ h
  · exact nomatch h

theorem annEq_mono (hg : Grows f g) (s c : Expr) (h : annEq f s c = true) : annEq g s c = true := by
  fun_induction annEq f s c with
  | case1 n l a b ih =>
    rw [annEq]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h ih ⊢
    rcases h with h | ⟨⟨hn, hi⟩, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨hn, annIdent_mono hg _ _ hi⟩, ih ha⟩
  | case2 n l a ih =>
    rw [annEq]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h ih ⊢
    rcases h with h | ⟨⟨hn, hi⟩, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨hn, annIdent_mono hg _ _ hi⟩, ih ha⟩
  | case3 c h1 h2 =>
    unfold annEq
    split
    · exact absurd rfl (h1 _ _ _ _)
    · exact absurd rfl (h2 _ _ _)
    · exact h

theorem paramsAnnEq_mono (hg : Grows f g) (cvj : ConstantVal) (cnP : Nat) (cv : ConstantVal) (rl : RecRule)
    (h : paramsAnnEq f cvj cnP cv rl = true) : paramsAnnEq g cvj cnP cv rl = true := by
  unfold paramsAnnEq at h ⊢
  split at h
  · exact listRel_mono (fun a b => annEq_mono hg a b) h
  · exact nomatch h

theorem iotaPartsRel_mono (hg : Grows f g) (cvj : ConstantVal) (cnP : Nat) (cv : ConstantVal) (rl : RecRule)
    (p' p : IotaParts) (h : iotaPartsRel f cvj cnP cv rl p' p = true) : iotaPartsRel g cvj cnP cv rl p' p = true := by
  unfold iotaPartsRel at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  refine ⟨h.1, h.2.elim Or.inl (fun h' => Or.inr ⟨⟨h'.1.1, paramsAnnEq_mono hg _ _ _ _ h'.1.2⟩,
    listRel_mono (fun a b => annEq_mono hg a b) h'.2⟩)⟩

theorem ruleReadsB_mono (hg : Grows f g) (cv : ConstantVal) (mI rP i : Nat) (rl : RecRule)
    (h : ruleReadsB f cv mI rP i rl = true) : ruleReadsB g cv mI rP i rl = true := by
  unfold ruleReadsB at h ⊢
  split at h
  · rename_i p' cvj cnP a b hp hf
    rw [hp, hg _ _ hf]
    simp only
    split at h
    · rename_i p hp2; exact iotaPartsRel_mono hg _ _ _ _ _ _ h
    · exact nomatch h
  · exact nomatch h

theorem forM_ok_of {α : Type} {f : α → Except CheckError Unit} :
    ∀ (l : List α), (∀ a ∈ l, f a = .ok ()) → l.forM f = .ok ()
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.forM, h a (List.mem_cons_self ..)]
    exact forM_ok_of l (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem recReadsOk_mono (hg : Grows f g) (ci : ConstantInfo) (h : recReadsOk f ci = .ok ()) :
    recReadsOk g ci = .ok () := by
  have hr := recReadsOk_reads h
  cases ci with
  | recInfo cv mI rP isK rules =>
    unfold recReadsOk
    refine forM_ok_of _ (fun ⟨rl, i⟩ hm => ?_)
    have hi := List.mem_zipIdx_iff_getElem?.mp hm
    have := ruleReadsB_mono hg cv mI rP i rl (hr cv mI rP isK rules rfl i rl (by simpa using hi))
    simp only [this]
    rfl
  | _ => rfl

theorem blockReadsOk_mono (hg : Grows f g) (p : BlockShape) (h : blockReadsOk f p = .ok ()) :
    blockReadsOk g p = .ok () :=
  forM_ok_of _ (fun ci hci => recReadsOk_mono hg ci (forM_except_ok h ci hci))

theorem grows_ext {X₁ X₂ : Env} (hx : EnvExt X₁ X₂) : Grows X₁.find? X₂.find? := hx.find

end ConPanqueque.Pipeline.IndExt
