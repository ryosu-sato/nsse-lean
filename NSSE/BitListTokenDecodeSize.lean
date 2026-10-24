import NSSE.BitListTokenDecode

namespace NSSE.BitListTokenDecodeSize

theorem many (count bs : List Bool) (tokens : List (List Bool)) (rest : List Bool)
    (h : (BitListTokenDecode.many count bs).1 = some (tokens,rest)) :
    2*(tokens.map List.length).sum + tokens.length + rest.length = bs.length := by
  induction count, bs using BitListTokenDecode.many.induct generalizing tokens rest with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    rw [BitListTokenDecode.many] at h
    dsimp only at h
    simp only [hc,Option.some.injEq] at h
    cases h
    simp
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    rw [BitListTokenDecode.many] at h
    dsimp only at h
    simp only [hc] at h
    split at h
    · simp at h
    · rename_i a rs hh; rw [hr] at hh; cases hh
  | case3 count bs c next hc r digits rs hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := BitListTokenReader.sizes bs digits rs hr
    rw [BitListTokenDecode.many] at h
    dsimp only at h
    simp only [hc] at h
    split at h
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i b ts hh
      have he := Option.some.inj (hr.symm.trans hh)
      cases he
      cases ht : (BitListTokenDecode.many next rs).1 with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨ys,us⟩ := p
        have hi := ih ys us ht
        have hp : (digits::ys,us)=(tokens,rest) := by simpa [ht] using h
        cases hp
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        omega

theorem parse (bs : List Bool) (tokens : List (List Bool)) (rest : List Bool)
    (h : (BitListTokenDecode.parse bs).1 = some (tokens,rest)) :
    2*(tokens.map List.length).sum + tokens.length + rest.length < bs.length := by
  simp only [BitListTokenDecode.parse] at h
  split at h
  · simp at h
  · rename_i count rs hr
    have hs := BitListTokenReader.sizes bs count rs hr
    have hm := many count rs tokens rest h
    omega

theorem decode (bs : List Bool) (tokens : List (List Bool))
    (h : (BitListTokenDecode.decode bs).1 = some tokens) :
    2*(tokens.map List.length).sum + tokens.length < bs.length := by
  simp only [BitListTokenDecode.decode] at h
  cases hp : (BitListTokenDecode.parse bs).1 with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨ts,rest⟩ := p
    have hs := parse bs ts rest hp
    cases rest with
    | nil => simp [hp] at h; cases h; simpa using hs
    | cons b rs => simp [hp] at h
end NSSE.BitListTokenDecodeSize
