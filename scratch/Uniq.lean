import ConPanqueque.ExprRep
open Flapjack ConPanqueque.Sep ConPanqueque.Rep

namespace ConPanqueque.Rep

theorem strAt_unique {h : Heap} {v : BitVec 64} {s s' : String} (ha : StrAt h v s) (hb : StrAt h v s') : s = s' := by
  obtain ⟨sz, ha⟩ := ha
  obtain ⟨sz', hb⟩ := hb
  have q1 : s.toUTF8.size = s.utf8ByteSize := by simp
  have q2 : s'.toUTF8.size = s'.utf8ByteSize := by simp
  have e0 := (ha 0 (by omega)).symm.trans (hb 0 (by omega))
  simp at e0
  have hsz : s.toUTF8.size = s'.toUTF8.size := by
    have := congrArg BitVec.toNat e0; simp at this; omega
  apply String.toByteArray_inj.mp
  apply ByteArray.ext
  apply Array.ext
  · simpa using hsz
  · intro i h1 h2
    have e := (ha (i + 1) (by simp at h1; omega)).symm.trans (hb (i + 1) (by simp at h2; omega))
    simp at e
    have := congrArg BitVec.toNat e
    simp at this
    have hh := UInt8.toNat_inj.mp this
    have i1 : i < s.toByteArray.data.size := h1
    have i2 : i < s'.toByteArray.data.size := h2
    simp only [ByteArray.get!] at hh
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem i1, Array.getElem?_eq_getElem i2] at hh
    simpa using hh

theorem natAt_unique {h h' : Heap} {v : BitVec 64} {n n' : Nat} (ha : NatAt h v n) (hb : NatAt h' v n') : n = n' := by
  obtain ⟨b1, e1⟩ := ha
  obtain ⟨b2, e2⟩ := hb
  have := congrArg BitVec.toNat (e1.symm.trans e2)
  simp at this; omega

end ConPanqueque.Rep

namespace ConPanqueque.Rep

theorem nameAt_unique {h : Heap} {p : BitVec 64} {n n' : ConLeche.Name} (hn : NameAt h p n) (hn' : NameAt h p n') :
    n = n' := by
  induction hn generalizing n' with
  | anonymous => cases hn' with
    | anonymous => rfl
    | str hp => exact absurd rfl hp
    | num hp => exact absurd rfl hp
  | str hp h0 h1 h2 h3 hpre hs ih =>
    cases hn' with
    | anonymous => exact absurd rfl hp
    | str _ h0' _ h2' h3' hpre' hs' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'
      rw [ih hpre', strAt_unique hs hs']
    | num _ h0' => rw [h0] at h0'; simp at h0'
  | num hp h0 h1 h2 h3 hpre hk ih =>
    cases hn' with
    | anonymous => exact absurd rfl hp
    | str _ h0' => rw [h0] at h0'; simp at h0'
    | num _ h0' _ h2' h3' hpre' hk' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'
      rw [ih hpre', natAt_unique hk hk']

theorem levelAt_unique {h : Heap} {p : BitVec 64} {u u' : ConLeche.Level} (hu : LevelAt h p u)
    (hu' : LevelAt h p u') : u = u' := by
  induction hu generalizing u' with
  | zero hp h0 h1 => cases hu' <;> simp_all
  | succ hp h0 h1 h2 hu ih =>
    cases hu' with
    | succ _ h0' _ h2' hu' => rw [h2] at h2'; simp at h2'; subst h2'; rw [ih hu']
    | _ => simp_all
  | max hp h0 h1 h2 h3 hu hv ih1 ih2 =>
    cases hu' with
    | max _ h0' _ h2' h3' hu' hv' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [ih1 hu', ih2 hv']
    | _ => simp_all
  | imax hp h0 h1 h2 h3 hu hv ih1 ih2 =>
    cases hu' with
    | imax _ h0' _ h2' h3' hu' hv' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [ih1 hu', ih2 hv']
    | _ => simp_all
  | param hp h0 h1 h2 hn =>
    cases hu' with
    | param _ h0' _ h2' hn' => rw [h2] at h2'; simp at h2'; subst h2'; rw [nameAt_unique hn hn']
    | _ => simp_all

end ConPanqueque.Rep

namespace ConPanqueque.Rep

theorem levelsAt_unique {h : Heap} {p : BitVec 64} {us us' : List ConLeche.Level} (ha : LevelsAt h p us)
    (hb : LevelsAt h p us') : us = us' := by
  induction ha generalizing us' with
  | nil => cases hb with
    | nil => rfl
    | cons hp => exact absurd rfl hp
  | cons hp h0 h1 hu hus ih =>
    cases hb with
    | nil => exact absurd rfl hp
    | cons _ h0' h1' hu' hus' =>
      rw [h0] at h0'; rw [h1] at h1'; simp at h0' h1'; subst h0'; subst h1'
      rw [levelAt_unique hu hu', ih hus']

theorem litAt_unique {h : Heap} {p : BitVec 64} {l l' : ConLeche.Literal} (ha : LitAt h p l) (hb : LitAt h p l') :
    l = l' := by
  cases ha with
  | natVal hp h0 h1 hn => cases hb with
    | natVal _ _ h1' hn' => rw [h1] at h1'; simp at h1'; subst h1'; rw [natAt_unique hn hn']
    | strVal _ h0' => rw [h0] at h0'; simp at h0'
  | strVal hp h0 h1 hs => cases hb with
    | natVal _ h0' => rw [h0] at h0'; simp at h0'
    | strVal _ _ h1' hs' => rw [h1] at h1'; simp at h1'; subst h1'; rw [strAt_unique hs hs']

theorem exprAt_unique {h : Heap} {p : BitVec 64} {e e' : ConLeche.Expr} (he : ExprAt h p e) (he' : ExprAt h p e') :
    e = e' := by
  induction he generalizing e' with
  | bvar hp h0 hd h2 hi =>
    cases he' with
    | bvar _ _ _ h2' hi' => rw [h2] at h2'; simp at h2'; subst h2'; rw [natAt_unique hi hi']
    | _ => simp_all
  | fvar hp h0 hd h2 h3 hi hty ih =>
    cases he' with
    | fvar _ _ _ h2' h3' hi' hty' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [natAt_unique hi hi', ih hty']
    | _ => simp_all
  | sort hp h0 hd h2 hu =>
    cases he' with
    | sort _ _ _ h2' hu' => rw [h2] at h2'; simp at h2'; subst h2'; rw [levelAt_unique hu hu']
    | _ => simp_all
  | const hp h0 hd h2 h3 hn hus =>
    cases he' with
    | const _ _ _ h2' h3' hn' hus' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'
      rw [nameAt_unique hn hn', levelsAt_unique hus hus']
    | _ => simp_all
  | app hp h0 hd h2 h3 ha hb iha ihb =>
    cases he' with
    | app _ _ _ h2' h3' ha' hb' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [iha ha', ihb hb']
    | _ => simp_all
  | lam hp h0 hd h2 h3 ha hb iha ihb =>
    cases he' with
    | lam _ _ _ h2' h3' ha' hb' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [iha ha', ihb hb']
    | _ => simp_all
  | forallE hp h0 hd h2 h3 ha hb iha ihb =>
    cases he' with
    | forallE _ _ _ h2' h3' ha' hb' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [iha ha', ihb hb']
    | _ => simp_all
  | letE hp h0 hd h2 h3 h4 ha hb hc iha ihb ihc =>
    cases he' with
    | letE _ _ _ h2' h3' h4' ha' hb' hc' =>
      rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'; simp at h2' h3' h4'; subst h2'; subst h3'; subst h4'
      rw [iha ha', ihb hb', ihc hc']
    | _ => simp_all
  | lit hp h0 hd h2 hl =>
    cases he' with
    | lit _ _ _ h2' hl' => rw [h2] at h2'; simp at h2'; subst h2'; rw [litAt_unique hl hl']
    | _ => simp_all
  | proj hp h0 hd h2 h3 h4 hn hi he ih =>
    cases he' with
    | proj _ _ _ h2' h3' h4' hn' hi' he' =>
      rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'; simp at h2' h3' h4'; subst h2'; subst h3'; subst h4'
      rw [nameAt_unique hn hn', natAt_unique hi hi', ih he']
    | _ => simp_all

end ConPanqueque.Rep
