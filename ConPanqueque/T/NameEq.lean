import ConPanqueque.T.NView
import ConPanqueque.T.Copy
import ConPanqueque.T.Ex.Small
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Name equality by structure

`neq(a, b)`: equal handles answer `1`; otherwise both rows are read, compared from their second word
on (the string bytes or the number's limbs), and the prefixes compared recursively. It decides the
equality of the names the handles read back to, with no well-formedness assumption on the store.
-/

namespace ConPanqueque.T.NEq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM

def fNeq := ofString "nameEq"
def pNa := ofString "na"
def pNb := ofString "nb"

/-- `w := w ∧ row₁[i] = row₂[i]` for `i` from `bb` up to the row length. -/
def cmpLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv lB) (vv lRn))
    (.seq (.assign .local lX (.load .one (.op .add [vv lA1, .shift .lsl (vv lB) (.const 3)])))
      (.seq (.assign .local lY (.load .one (.op .add [vv lRp, .shift .lsl (vv lB) (.const 3)])))
        (.seq (.assign .local lW (.op .and [vv lW, .cmp .equal (vv lX) (vv lY)]))
          (.assign .local lB (.op .add [vv lB, .const 1])))))

/-- The flag after comparing words `1 … i` (`i` words). -/
def flagW (ws1 ws2 : List (BitVec 64)) (i : Nat) : BitVec 64 :=
  if ∀ j, j < i → ws1[j + 1]? = ws2[j + 1]? then 1 else 0

section
variable {σ : Type}

theorem flagW_succ (ws1 ws2 : List (BitVec 64)) (i : Nat) (h1 : i + 1 < ws1.length) (h2 : i + 1 < ws2.length) :
    flagW ws1 ws2 (i + 1) = flagW ws1 ws2 i &&&
      (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal ws1[i + 1] ws2[i + 1] then 1 else 0) := by
  unfold flagW
  by_cases hA : ∀ j, j < i → ws1[j + 1]? = ws2[j + 1]?
  · by_cases e : ws1[i + 1] = ws2[i + 1]
    · have : ∀ j, j < i + 1 → ws1[j + 1]? = ws2[j + 1]? := by
        intro j hj
        rcases Nat.lt_or_ge j i with hl | hg
        · exact hA j hl
        · have : j = i := by omega
          subst this; rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, e]
      rw [ite_eq_left this, ite_eq_left hA]; simp [e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : ¬ ∀ j, j < i + 1 → ws1[j + 1]? = ws2[j + 1]? := by
        intro h; have := h i (by omega)
        rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this; exact e (Option.some.inj this)
      rw [ite_eq_right this, ite_eq_left hA]; simp [e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : ¬ ∀ j, j < i + 1 → ws1[j + 1]? = ws2[j + 1]? := fun h => hA (fun j hj => h j (by omega))
    rw [ite_eq_right this, ite_eq_right hA]; simp

theorem cmpLoop_spec {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (ws1 ws2 : List (BitVec 64)) (P1 P2 : BitVec 64)
    (hlen : ws1.length = ws2.length) (hpos : 1 ≤ ws1.length) (hn : ws1.length < 2 ^ 61)
    (hm1 : ∀ i (hi : i < ws1.length), (P1 + BitVec.ofNat 64 (8 * i), ws1[i]) ∈ M)
    (hm2 : ∀ i (hi : i < ws2.length), (P2 + BitVec.ofNat 64 (8 * i), ws2[i]) ∈ M)
    (ha1 : Γ.get lA1 = some P1) (hrp : Γ.get lRp = some P2) (hrn : Γ.get lRn = some (BitVec.ofNat 64 ws1.length))
    (hx : Γ.get lX = none) (hy : Γ.get lY = none)
    (hr : SpecR (Inv C s ((lB, BitVec.ofNat 64 ws1.length) :: (lW, flagW ws1 ws2 (ws1.length - 1)) :: Γ) M DI)
      rest s m R) :
    SpecR (Inv C s ((lB, BitVec.ofNat 64 (0 + 1)) :: (lW, flagW ws1 ws2 0) :: Γ) M DI) (.seq cmpLoop rest) s m R := by
  have hr' : SpecR (Inv C s ((lB, BitVec.ofNat 64 ((ws1.length - 1) + 1)) ::
      (lW, flagW ws1 ws2 (ws1.length - 1)) :: Γ) M DI) rest s m R := by
    rw [show ws1.length - 1 + 1 = ws1.length by omega]; exact hr
  refine specR_forI (σ := σ) (D := DI) (M := M) _ _ rest (ws1.length - 1) (fun _ => C)
    (fun i => (lB, BitVec.ofNat 64 (i + 1)) :: (lW, flagW ws1 ws2 i) :: Γ)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 (i + 1))
      (BitVec.ofNat 64 ws1.length) then 1 else 0, by simp +decide [sev, hrn], ?_⟩) (fun i hi => ?_) hr'
  · have e : (BitVec.ofNat 64 (i + 1) < BitVec.ofNat 64 ws1.length) ↔ i + 1 < ws1.length := by
      rw [BitVec.lt_def]; simp; omega
    by_cases h : i + 1 < ws1.length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h]; omega
    · have : ¬ BitVec.ofNat 64 (i + 1) < BitVec.ofNat 64 ws1.length := fun x => h (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]; omega
  have hi1 : i + 1 < ws1.length := by omega
  have hi2 : i + 1 < ws2.length := by omega
  have addr : ∀ P : BitVec 64, P + BitVec.ofNat 64 (i + 1) <<< (3 : BitVec 64).toNat = P + BitVec.ofNat 64 (8 * (i + 1)) := by
    intro P; rw [show (3 : BitVec 64).toNat = 3 from rfl, shl_ofNat _ _ (by omega)]
  refine step_seq (step_loadI lX _ (P1 + BitVec.ofNat 64 (8 * (i + 1))) ws1[i + 1] (by decide)
    (by simp +decide [sev, ha1]; rw [shl_ofNat _ _ (by omega)]) (hm1 _ hi1)) ?_
  refine step_seq (step_loadI lY _ (P2 + BitVec.ofNat 64 (8 * (i + 1))) ws2[i + 1] (by decide)
    (by simp +decide [sev, hrp]; rw [shl_ofNat _ _ (by omega)]) (hm2 _ hi2)) ?_
  refine step_seq (step_assignI lW _ (flagW ws1 ws2 (i + 1)) (by decide)
    (by simp +decide [sev]; rw [flagW_succ ws1 ws2 i hi1 hi2]; rfl)) ?_
  refine step_mono (step_assignI lB _ (BitVec.ofNat 64 (i + 1 + 1)) (by decide)
    (by simp +decide [sev]; exact word_add1_eq (i + 1))) (fun _ h => h) (fun t ht => ?_)
  refine inv_envMono ht (fun z v hz => ?_)
  simp only [Env.get_cons] at hz ⊢
  by_cases h1 : z = lB
  · simp_all
  by_cases h2 : z = lW
  · subst h2; simp_all [show lW ≠ lB by decide]
  by_cases h3 : z = lY
  · subst h3; simp_all
  by_cases h4 : z = lX
  · subst h4; simp_all
  simp_all

end

def neqTail : ProgHOL 64 :=
  .ite (.cmp .notEqual (vv lA3) (vv lDg)) (.return (.const 0))
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 1))
  (.ite (.cmp .notEqual (vv lA2) (vv lRn)) (.return (.const 0))
  (.seq (.assign .local lW (.const 1)) (.seq (.assign .local lB (.const 1))
  (.seq cmpLoop
  (.ite (.cmp .equal (vv lW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local lX (.load .one (vv lA1))) (.seq (.assign .local lY (.load .one (vv lRp)))
  (.seq (.call (some (some (.local, lZ), none)) fNeq [vv lX, vv lY]) (.return (vv lZ)))))))))))

def neqCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pNa) (vv pNb)) (.return (.const 1))
  (.seq (.assign .local lFl (vv lFln))
  (.seq (.assign .local lDh (vv pNa)) (.seq nViewP
  (.seq (.assign .local lA1 (vv lRp)) (.seq (.assign .local lA2 (vv lRn)) (.seq (.assign .local lA3 (vv lDg))
  (.seq (.assign .local lDh (vv pNb)) (.seq nViewP neqTail))))))))

def neqBody : ProgHOL 64 := prologue inst1Locals neqCore

section
variable {σ : Type}

theorem flagW_zero (ws1 ws2 : List (BitVec 64)) : flagW ws1 ws2 0 = 1 := by simp [flagW]

theorem flagW_full (ws1 ws2 : List (BitVec 64)) (hl : ws1.length = ws2.length) (hpos : 1 ≤ ws1.length) :
    flagW ws1 ws2 (ws1.length - 1) ≠ 0 ↔ ws1.tail = ws2.tail := by
  unfold flagW
  constructor
  · intro h
    have hA : ∀ j, j < ws1.length - 1 → ws1[j + 1]? = ws2[j + 1]? := by
      by_cases hc : ∀ j, j < ws1.length - 1 → ws1[j + 1]? = ws2[j + 1]?
      · exact hc
      · rw [ite_eq_right hc] at h; exact absurd rfl h
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_tail, List.getElem?_tail]
    rcases Nat.lt_or_ge j (ws1.length - 1) with hj | hj
    · exact hA j hj
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro h
    have hA : ∀ j, j < ws1.length - 1 → ws1[j + 1]? = ws2[j + 1]? := by
      intro j _; rw [← List.getElem?_tail, ← List.getElem?_tail, h]
    rw [ite_eq_left hA]; decide

/-- After both views, the tags equal and nonzero: compare the tails, then the prefixes. -/
theorem neqTail_spec (C : Ctx) (hcode : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    {s : AState} {Γ : Env} {M : Mem} (tag : Nat) (htag : 0 < tag) (htag8 : tag < 8)
    (pa pb : NIdx) (tl1 tl2 : List (BitVec 64)) (qa qb : ConLeche.Name) (P1 P2 : BitVec 64)
    (hn1 : 1 + tl1.length < 2 ^ 61) (hn2 : 1 + tl2.length < 2 ^ 61)
    (hm1 : ∀ i (hi : i < (Enc.idxW pa :: tl1).length), (P1 + BitVec.ofNat 64 (8 * i), (Enc.idxW pa :: tl1)[i]) ∈ M)
    (hm2 : ∀ i (hi : i < (Enc.idxW pb :: tl2).length), (P2 + BitVec.ofNat 64 (8 * i), (Enc.idxW pb :: tl2)[i]) ∈ M)
    (ha1 : Γ.get lA1 = some P1) (ha2 : Γ.get lA2 = some (BitVec.ofNat 64 (1 + tl1.length)))
    (ha3 : Γ.get lA3 = some (BitVec.ofNat 64 tag)) (hdg : Γ.get lDg = some (BitVec.ofNat 64 tag))
    (hrp : Γ.get lRp = some P2) (hrn : Γ.get lRn = some (BitVec.ofNat 64 (1 + tl2.length)))
    (hx : Γ.get lX = none) (hy : Γ.get lY = none)
    (hrec : SpecR (Pre (σ := σ) C s [(pNa, Enc.idxW pa), (pNb, Enc.idxW pb)]) neqBody s (pure (decide (qa = qb)))
      (PostB C)) :
    SpecR (Inv (σ := σ) C s Γ M DI) neqTail s (pure (decide (qa = qb ∧ tl1 = tl2))) (PostB C) := by
  unfold neqTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha3, hdg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  have ht0 : BitVec.ofNat 64 tag ≠ 0#64 := ofNat_ne_zero tag (by omega) (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, hdg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ht0])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  by_cases hl : tl1.length = tl2.length
  · have hlw : BitVec.ofNat 64 (1 + tl1.length) = BitVec.ofNat 64 (1 + tl2.length) := by rw [hl]
    refine specR_ifI _ 0 (by simp only [sev, Env.get, sev_vv, ha2, hrn, Option.bind_some, hlw,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; simp)
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_assignI lW (.const 1) 1 (by decide) rfl ?_
    refine specR_assignI lB (.const 1) (BitVec.ofNat 64 (0 + 1)) (by decide) rfl ?_
    rw [← flagW_zero (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2)]
    refine cmpLoop_spec (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) P1 P2 (by simp [hl]) (by simp) (by simp; omega)
      hm1 hm2 (by simp +decide [ha1]) (by simp +decide [hrp]) (by simp +decide [hrn]; rw [hl, Nat.add_comm])
      (by simp +decide [hx]) (by simp +decide [hy]) ?_
    have hf := flagW_full (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) (by simp [hl]) (by simp)
    simp only [List.tail_cons] at hf
    by_cases ht : tl1 = tl2
    · have hfw : flagW (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) ((Enc.idxW pa :: tl1).length - 1) ≠ 0 := hf.mpr ht
      have hfw' : flagW (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) tl1.length ≠ 0 := by simpa using hfw
      refine specR_ifI _ 0 ?_ (fun hw => absurd rfl hw) (fun _ => ?_)
      · simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hfw'
      refine specR_loadI' lX (vv lA1) P1 (P1 + BitVec.ofNat 64 (8 * 0)) (Enc.idxW pa) (by decide)
        (by simp +decide [ha1]) (by simp) (hm1 0 (by simp)) ?_
      refine specR_loadI' lY (vv lRp) P2 (P2 + BitVec.ofNat 64 (8 * 0)) (Enc.idxW pb) (by decide)
        (by simp +decide [hrp]) (by simp) (hm2 0 (by simp)) ?_
      refine specR_congr (m' := pure (decide (qa = qb)) >>= fun b => pure b) (by simp [ht]) ?_
      refine specR_call2IM lZ fNeq pNa pNb (by decide) _ _ neqBody (Enc.idxW pa) (Enc.idxW pb) (by decide) hcode
        (by simp +decide) (by simp +decide) (PostB C) (fun _ _ _ _ hp => hp.2)
        (fun u hu _ h1 h2 w hw => by subst hw; exact hrec _ (pre2 hu _ _ _ _ h1 h2))
        (fun r w s' st hp => ?_)
      obtain ⟨rfl, _⟩ := hp
      exact specR_returnI (vv lZ) _ (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hfw : flagW (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) ((Enc.idxW pa :: tl1).length - 1) = 0 := by
        by_cases c : flagW (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) ((Enc.idxW pa :: tl1).length - 1) = 0
        · exact c
        · exact absurd (hf.mp c) ht
      have hfw' : flagW (Enc.idxW pa :: tl1) (Enc.idxW pb :: tl2) tl1.length = 0 := by simpa using hfw
      refine specR_ifI _ 1 ?_ (fun _ => ?_) (fun hw => absurd hw (by decide))
      · simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfw']
      refine specR_congr (m' := pure false) (by simp [ht]) ?_
      exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : BitVec.ofNat 64 (1 + tl1.length) ≠ BitVec.ofNat 64 (1 + tl2.length) := fun e =>
      hl (by have := (word_eq_iff _ _ (by omega) (by omega)).mp e; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, ha2, hrn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_congr (m' := pure false)
      (by simp only [show ¬(qa = qb ∧ tl1 = tl2) from fun h => hl (by rw [h.2]), decide_false]) ?_
    exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem params_noneNE (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pNa, va), (pNb, vb)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

def nameTag : ConLeche.Name → Nat
  | .anonymous => 0 | .str _ _ => 1 | .num _ _ => 2

theorem nameTag_of (st : NStore) (f : Nat) (i : NIdx) (x : ConLeche.Name) (v : NNodeView)
    (hd : denoteNAux st f i = some x) (hv : st.view i = some v) : nameTag x = v.tagN := by
  rcases denoteNAux_cases st f i x v hd hv with ⟨rfl, rfl⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ <;> rfl

theorem neqTail_diff {C : Ctx} {s : AState} {Γ : Env} {M : Mem} (t1 t2 : Nat) (h12 : t1 ≠ t2) (h1 : t1 < 8)
    (h2 : t2 < 8) (b : Bool) (hb : b = false)
    (ha3 : Γ.get lA3 = some (BitVec.ofNat 64 t1)) (hdg : Γ.get lDg = some (BitVec.ofNat 64 t2)) :
    SpecR (Inv (σ := σ) C s Γ M DI) neqTail s (pure b) (PostB C) := by
  subst hb
  unfold neqTail
  have hne : BitVec.ofNat 64 t1 ≠ BitVec.ofNat 64 t2 := fun e =>
    h12 ((word_eq_iff t1 t2 (by omega) (by omega)).mp e)
  refine specR_ifI _ 1 (by simp +decide [sev, ha3, hdg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun _ => ?_) (fun hw => absurd hw (by decide))
  exact specR_returnI (.const 0) 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem neqTail_zero {C : Ctx} {s : AState} {Γ : Env} {M : Mem} (b : Bool) (hb : b = true)
    (ha3 : Γ.get lA3 = some (BitVec.ofNat 64 0)) (hdg : Γ.get lDg = some (BitVec.ofNat 64 0)) :
    SpecR (Inv (σ := σ) C s Γ M DI) neqTail s (pure b) (PostB C) := by
  subst hb
  unfold neqTail
  refine specR_ifI _ 0 (by simp +decide [sev, ha3, hdg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_ifI _ 1 (by simp +decide [sev, hdg, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun hw => absurd hw (by decide))
  exact specR_returnI (.const 1) 1 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The two views, then the tail; equal handles answer at once. -/
theorem neq_views (C : Ctx) (x y : ConLeche.Name) (a b : NIdx) (fa fb : Nat) (s : AState)
    (hda : denoteNAux s.store.ns fa a = some x) (hdb : denoteNAux s.store.ns fb b = some y)
    (hk : ∀ va vb P1 P2, s.store.ns.view a = some va → s.store.ns.view b = some vb →
      (encNView va).length < 2 ^ 61 → (encNView vb).length < 2 ^ 61 →
      ∀ Γ : Env, Γ.get lA1 = some P1 → Γ.get lA2 = some (BitVec.ofNat 64 (encNView va).length) →
        Γ.get lA3 = some (BitVec.ofNat 64 va.tagN) → Γ.get lDg = some (BitVec.ofNat 64 vb.tagN) →
        Γ.get lRp = some P2 → Γ.get lRn = some (BitVec.ofNat 64 (encNView vb).length) →
        Γ.get lX = none → Γ.get lY = none →
        SpecR (Inv (σ := σ) C s Γ (wordsAt P2 (encNView vb) ++ (wordsAt P1 (encNView va) ++ [])) DI) neqTail s
          (pure (decide (x = y))) (PostB C)) :
    SpecR (Pre (σ := σ) C s [(pNa, Enc.idxW a), (pNb, Enc.idxW b)]) neqBody s (pure (decide (x = y))) (PostB C) := by
  refine specR_prologue (postB_locals C) (params_noneNE _ _ C) ?_
  unfold neqCore
  by_cases hab : a = b
  · subst hab
    have e : x = y := denoteNAux_det _ _ _ _ _ _ hda hdb
    refine specR_ifI _ 1 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun hw => absurd hw (by decide))
    exact specR_returnI (.const 1) 1 rfl (fun t ht => ⟨by simp [e], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne : Enc.idxW a ≠ Enc.idxW b := fun e => hab (Enc.idxW_inj e)
  refine specR_ifI _ 0 (by simp +decide [sev, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun hw => absurd rfl hw) (fun _ => ?_)
  refine specR_assignI lFl (vv lFln) C.FLn (by decide) rfl ?_
  refine specR_assignI lDh (vv pNa) (Enc.idxW a) (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_nviewPI a (by simp) (by simp +decide) (by simp +decide [ctxEnv]) (by decide)
    (fun va P1 hva _ hsa => ?_)
  refine specR_assignI lA1 (vv lRp) P1 (by decide) (by simp) ?_
  refine specR_assignI lA2 (vv lRn) (BitVec.ofNat 64 (encNView va).length) (by decide) (by simp +decide) ?_
  refine specR_assignI lA3 (vv lDg) (BitVec.ofNat 64 va.tagN) (by decide) (by simp +decide) ?_
  refine specR_assignI lDh (vv pNb) (Enc.idxW b) (by decide) (by simp +decide [ctxEnv]) ?_
  refine specR_nviewPI b (by simp) (by simp +decide) (by simp +decide [ctxEnv]) (by decide)
    (fun vb P2 hvb _ hsb => ?_)
  exact hk va vb P1 P2 hva hvb hsa hsb _ (by simp +decide) (by simp +decide) (by simp +decide) (by simp +decide)
    (by simp +decide) (by simp +decide) (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv])

/-- `nameEq` decides the equality of the read-back names. -/
theorem neq_spec (C : Ctx) (hcode : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one)) :
    ∀ (x : ConLeche.Name) (a b : NIdx) (y : ConLeche.Name) (fa fb : Nat) (s : AState),
      denoteNAux s.store.ns fa a = some x → denoteNAux s.store.ns fb b = some y →
      SpecR (Pre (σ := σ) C s [(pNa, Enc.idxW a), (pNb, Enc.idxW b)]) neqBody s (pure (decide (x = y)))
        (PostB C) := by
  intro x
  induction x with
  | anonymous =>
    intro a b y fa fb s hda hdb
    refine neq_views C .anonymous y a b fa fb s hda hdb (fun va vb P1 P2 hva hvb _ _ Γ h1 h2 h3 h4 h5 h6 h7 h8 => ?_)
    have hta := nameTag_of _ _ _ _ _ hda hva
    have htb := nameTag_of _ _ _ _ _ hdb hvb
    simp only [nameTag] at hta
    by_cases hy0 : vb.tagN = 0
    · have hy : y = .anonymous := by
        cases y with
        | anonymous => rfl
        | str _ _ => simp [nameTag] at htb; omega
        | num _ _ => simp [nameTag] at htb; omega
      exact neqTail_zero _ (by simp [hy]) (by rw [← hta] at h3; exact h3) (by rw [hy0] at h4; exact h4)
    · have hlt : vb.tagN < 3 := by cases vb <;> simp [NNodeView.tagN]
      refine neqTail_diff va.tagN vb.tagN (by omega) (by omega) (by omega) _ ?_ h3 h4
      simp only [decide_eq_false_iff_not]; intro e; subst e; simp [nameTag] at htb; omega
  | str q str ih =>
    intro a b y fa fb s hda hdb
    refine neq_views C (.str q str) y a b fa fb s hda hdb
      (fun va vb P1 P2 hva hvb hsa hsb Γ h1 h2 h3 h4 h5 h6 h7 h8 => ?_)
    rcases denoteNAux_cases _ _ _ _ _ hda hva with ⟨_, hx⟩ | ⟨pa, sa, qa, fa', rfl, hx, hqa⟩ | ⟨_, _, _, _, _, hx, _⟩
    · cases hx
    · injection hx with hq hs; subst hq hs
      rcases denoteNAux_cases _ _ _ _ _ hdb hvb with ⟨rfl, rfl⟩ | ⟨pb, sb, qb, fb', rfl, rfl, hqb⟩ |
        ⟨pb, nb, qb, fb', rfl, rfl, hqb⟩
      · exact neqTail_diff 1 0 (by decide) (by decide) (by decide) _ (by simp) h3 h4
      · refine specR_congr (m' := pure (decide (q = qb ∧ Enc.strW str = Enc.strW sb))) ?_ ?_
        · have : (ConLeche.Name.str q str = .str qb sb) ↔ (q = qb ∧ Enc.strW str = Enc.strW sb) := by
            constructor
            · intro e; injection e with e1 e2; exact ⟨e1, by rw [e2]⟩
            · rintro ⟨e1, e2⟩; rw [e1, Enc.strW_inj e2]
          simp only [this]
        exact neqTail_spec C hcode 1 (by decide) (by decide) pa pb (Enc.strW str) (Enc.strW sb) q qb P1 P2
          (by simpa [encNView, Enc.encStr, Nat.add_comm] using hsa) (by simpa [encNView, Enc.encStr, Nat.add_comm] using hsb)
          (fun i hi => List.mem_append_right _ (wordsAt_get P1 (Enc.idxW pa :: Enc.strW str) i hi []))
          (fun i hi => wordsAt_get P2 (Enc.idxW pb :: Enc.strW sb) i hi _)
          h1 (by simpa [encNView, Enc.encStr, Nat.add_comm] using h2) h3 h4 h5
          (by simpa [encNView, Enc.encStr, Nat.add_comm] using h6) h7 h8 (ih pa pb qb fa' fb' s hqa hqb)
      · exact neqTail_diff 1 2 (by decide) (by decide) (by decide) _ (by simp) h3 h4
    · cases hx
  | num q n ih =>
    intro a b y fa fb s hda hdb
    refine neq_views C (.num q n) y a b fa fb s hda hdb
      (fun va vb P1 P2 hva hvb hsa hsb Γ h1 h2 h3 h4 h5 h6 h7 h8 => ?_)
    rcases denoteNAux_cases _ _ _ _ _ hda hva with ⟨_, hx⟩ | ⟨_, _, _, _, _, hx, _⟩ | ⟨pa, na, qa, fa', rfl, hx, hqa⟩
    · cases hx
    · cases hx
    · injection hx with hq hs; subst hq hs
      rcases denoteNAux_cases _ _ _ _ _ hdb hvb with ⟨rfl, rfl⟩ | ⟨pb, sb, qb, fb', rfl, rfl, hqb⟩ |
        ⟨pb, nb, qb, fb', rfl, rfl, hqb⟩
      · exact neqTail_diff 2 0 (by decide) (by decide) (by decide) _ (by simp) h3 h4
      · exact neqTail_diff 2 1 (by decide) (by decide) (by decide) _ (by simp) h3 h4
      · refine specR_congr (m' := pure (decide (q = qb ∧ Enc.limbs n = Enc.limbs nb))) ?_ ?_
        · have : (ConLeche.Name.num q n = .num qb nb) ↔ (q = qb ∧ Enc.limbs n = Enc.limbs nb) := by
            constructor
            · intro e; injection e with e1 e2; exact ⟨e1, by rw [e2]⟩
            · rintro ⟨e1, e2⟩; rw [e1, Enc.limbs_inj e2]
          simp only [this]
        exact neqTail_spec C hcode 2 (by decide) (by decide) pa pb (Enc.limbs n) (Enc.limbs nb) q qb P1 P2
          (by simpa [encNView, Enc.encNum, Nat.add_comm] using hsa) (by simpa [encNView, Enc.encNum, Nat.add_comm] using hsb)
          (fun i hi => List.mem_append_right _ (wordsAt_get P1 (Enc.idxW pa :: Enc.limbs n) i hi []))
          (fun i hi => wordsAt_get P2 (Enc.idxW pb :: Enc.limbs nb) i hi _)
          h1 (by simpa [encNView, Enc.encNum, Nat.add_comm] using h2) h3 h4 h5
          (by simpa [encNView, Enc.encNum, Nat.add_comm] using h6) h7 h8 (ih pa pb qb fa' fb' s hqa hqb)

end

end ConPanqueque.T.NEq
