import ConPanqueque.Start.Main2
import ConPanqueque.Pipeline.Prepare
import ConPanqueque.Pipeline.NameInj

/-! # From name words to names

The pass compares handle words.  With the pin table's denotation (`PinsOK`), persistence, and
canonical handles (`denoteN_inj`), a record whose name word differs from every pinned cell's word
has a name outside `FN`, the pinned names, the reserved names and `Bool.rec` (`name_notMem`). -/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConPanqueque.V ConPanqueque.T

namespace ConPanqueque.Start

def boolRecName : ConLeche.Name := (ConLeche.Name.anonymous.str "Bool").str "rec"

/-- The forbidden names. -/
def FN : List ConLeche.Name := pinNames ++ reservedBasisNameValues ++ [boolRecName]

theorem denoteNL_get {st : EStore} : ∀ {hs : List NIdx} {xs : List ConLeche.Name}, denoteNL st hs xs →
    hs.length = xs.length ∧ ∀ i (hi : i < xs.length) (hi' : i < hs.length), denoteN st.ns hs[i] = some xs[i]
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | h :: hs, x :: xs, ⟨h1, h2⟩ => by
    obtain ⟨hl, hg⟩ := denoteNL_get h2
    refine ⟨by simp [hl], fun i hi hi' => ?_⟩
    cases i with
    | zero => exact h1
    | succ i => exact hg i (by simpa using hi) (by simpa using hi')
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **A checked name word is a name outside `FN`.** -/
theorem name_notMem (st : EStore) (hwf : NStoreWF st.ns) (P : Pins) (EH : List (BitVec 64)) (hb : PinBlock EH P)
    (hdn : denoteNL st P.names.toList pinNames) (hdr : denoteNL st P.reserved reservedBasisNameValues)
    (hpn : ∀ n ∈ P.names, PersN n) (hpr : PersNList P.reserved)
    (bh : NIdx) (hB : EH[138]? = some (Enc.idxW bh)) (hbd : denoteN st.ns bh = some boolRecName) (hbp : PersN bh)
    (h : NIdx) (n : ConLeche.Name) (hp : PersN h) (hd : denoteN st.ns h = some n)
    (hforb : ∀ j ∈ cellsF, EH[j]? ≠ some (Enc.idxW h)) : n ∉ FN := by
  intro hn
  simp only [FN, List.mem_append, List.mem_singleton] at hn
  rcases hn with (hn | hn) | hn
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
    obtain ⟨hl, hg⟩ := denoteNL_get hdn
    have hi' : i < P.names.size := by simp at hl; omega
    have hg' : denoteN st.ns P.names[i] = some pinNames[i] := by
      have := hg i hi (by simpa using hi'); simpa using this
    have e := ConPanqueque.Pipeline.denoteN_inj hwf hp (hpn _ (Array.getElem_mem hi')) hd hg'
    have h52 : i < 52 := by have := pinNames_length; omega
    exact hforb (64 + i) (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h52, rfl⟩)))
      (by rw [hb.names i hi', e])
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
    obtain ⟨hl, hg⟩ := denoteNL_get hdr
    have hi' : i < P.reserved.length := by omega
    have e := ConPanqueque.Pipeline.denoteN_inj hwf hp (hpr _ (List.getElem_mem hi')) hd (hg i hi hi')
    have h16 : i < 16 := by have := reserved_length; omega
    exact hforb (122 + i) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h16, rfl⟩)))
      (by rw [hb.res i hi', e])
  · subst hn
    have e := ConPanqueque.Pipeline.denoteN_inj hwf hp hbp hd hbd
    exact hforb 138 (by simp [cellsF]) (by rw [hB, e])

/-- The names the environment's guards read are all forbidden. -/
theorem guards_sub : (ConLeche.natOpNames ++ ConLeche.natDivModNames ++ ConLeche.reduceOpNames ++
    [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName, ConLeche.boolTrueName, ConLeche.boolFalseName]).all (fun m => FN.contains m) = true := by
  decide +kernel

theorem nameOK_of_notMem {n : ConLeche.Name} (h : n ∉ FN) : ConPanqueque.Pipeline.NameOK n := by
  have hs := guards_sub
  simp only [List.all_eq_true, List.contains_iff_mem, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hs
  have nm : ∀ m, (m ∈ ConLeche.natOpNames ∨ m ∈ ConLeche.natDivModNames ∨ m ∈ ConLeche.reduceOpNames ∨ m = ConLeche.natName ∨ m = ConLeche.natZeroName ∨
      m = ConLeche.natSuccName ∨ m = ConLeche.boolTrueName ∨ m = ConLeche.boolFalseName) → m ≠ n := by
    intro m hm e; subst e; apply h
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
    · exact hs m (Or.inl (Or.inl (Or.inl hm)))
    · exact hs m (Or.inl (Or.inl (Or.inr hm)))
    · exact hs m (Or.inl (Or.inr hm))
    · exact hs m (Or.inr (Or.inl hm))
    · exact hs m (Or.inr (Or.inr (Or.inl hm)))
    · exact hs m (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    · exact hs m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
    · exact hs m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm)))))
  refine ⟨?_, fun hm => nm n (Or.inr (Or.inr (Or.inl hm))) rfl, fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) e.symm,
    fun e => nm _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) e.symm⟩
  simp only [ConLeche.natOpName, Bool.or_eq_false_iff]
  -- `List.contains` on names
  constructor
  · cases hc : ConLeche.natOpNames.contains n
    · rfl
    · exfalso; exact nm n (Or.inl (by simpa using hc)) rfl
  · cases hc : ConLeche.natDivModNames.contains n
    · rfl
    · exfalso; exact nm n (Or.inr (Or.inl (by simpa using hc))) rfl

end ConPanqueque.Start
