/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 3.2.3: the relations on `0, …, 3, c, d`

For the first odd entries `a < b ≤ 3 < c < d` of `s` and the two odd entries
`α < β ≤ 3` of `K_[0,1,2,3] s` (twelve configurations, Lemma A.3), and the
signs `x, y, p, q` of `α, β, a, b` (eight patterns of a fixed parity each),

  `K_[α,β,c,d] (−1)_[α]^x (−1)_[β]^y K_[0,1,2,3] ≈ X K_[0,1,2,c] Y K_[a,b,c,d] (−1)_[a]^p (−1)_[b]^q`

with `X`, `Y` words of `(−1)` and `X` letters (Proposition A.15).  Each is
reduced to the one instance of (5a) on `0, 1, 2, 3, c, d`,
`K_[0,1,2,3] K_[1,3,c,d] ≈ K_[2,3,c,d] K_[0,1,2,c]`, by moving signed
permutations through the `K`s; the chains are found by a search script
(scratch), checked by the kernel on `0, …, 5` and moved along an order
embedding.
-/
import QCert.LiRossSelinger.Derive
import QCert.LiRossSelinger.PathSP

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-- `X` for `{a,b} = {0,1}`, `{α,β} = {0,2}`. -/
def X323_0102 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | false, true, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | false, true, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,1}`, `{α,β} = {0,2}`. -/
def Y323_0102 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, true => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 2, Gen.neg 4]
  | false, true, false, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 3]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 2]
  | true, true, false, false => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 3, Gen.neg 4]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,1}`, `{α,β} = {0,2}`. -/
def S323_0102 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    stepsOf 6 [1696662018, 131073, 3211264, 36766084, 4391168, 37945988, 70320201, 36766084,
      6619392, 40174212, 27163494279, 1697711760, 27182302605, 27182302348, 1698890642, 1680933891,
      105055626, 105055498, 105055497, 6489728, 6424326, 3278342, 70321225, 36767108,
      3212939, 2163974, 18020173959, 1126238103, 1126237597, 1126237336, 70386954, 70386953,
      4327040, 3278470, 36767492, 3213003, 52495690, 4327435, 21104388, 70387337,
      70387338, 4262150, 67713, 4327430, 4393222, 264833, 37947268, 4393035,
      4393344, 4392966, 264577, 6490246, 4326987, 104990596, 69272964, 102827652,
      27146783111, 27181254797, 27181254540, 1698825625, 1696663299, 69273226, 1698826243, 4327296,
      434917934227, 1698890626]
  | false, false, true, true =>
    stepsOf 6 [131585, 66049, 2163590, 2163334, 1696662530, 131073, 2162688, 2163083,
      3277056, 20054660, 4391424, 21169028, 70385993, 20054660, 6619648, 23397252,
      27163494791, 27164477580, 1697777552, 27182368397, 27182368140, 1698890898, 1680999683, 105055882,
      105055754, 105055753, 6489984, 102828036, 52496132, 1126237699, 52495754, 6424838,
      3278854, 52495626, 1126237827, 2164619, 52496516, 70387017, 18020174471, 1126238608,
      1126238110, 1126237845, 1126237590, 70387338, 1126237955, 69273226, 4393088, 21104516,
      4327499, 54659460, 4328075, 4328320, 4392966, 4327686, 3278854, 3278982,
      4327814, 133761, 264577, 6424838, 3278854, 2164614, 3213446, 6359430,
      68225, 6490246, 2164992, 102828036, 2164683, 69273289, 27146783623, 1696664208,
      1696663711, 27181254541, 27181254284, 69273546, 104925321, 104925322, 1113655043, 104990922,
      106039753, 1683097603, 6426315, 90311940, 6425611, 23202564, 106039882, 1683097859,
      5376128, 6621958, 6425606, 5376774, 5376902, 6425734, 134529, 396417,
      5442310, 434917934483, 1698890882]
  | false, true, false, true =>
    stepsOf 6 [131841, 1696662530, 262145, 2162688, 69271940, 4391168, 4391563, 27163624839,
      27164476556, 27182367629, 1126237187, 4392454, 1126237315, 52495748, 69273220, 4392011,
      4392331, 4391942, 1126238096, 1126237842, 1126237338, 4327040, 4327430, 132993,
      27146848135, 27181254285, 27182302604, 434917934035, 1698890882]
  | false, true, true, false =>
    stepsOf 6 [66305, 1696662530, 131073, 2162688, 2163083, 4391168, 21168772, 27163493767,
      27164476556, 27182367629, 1126237187, 1126237315, 2164107, 52496004, 1126238096, 1126237598,
      1126237330, 69272970, 70387210, 70387209, 21104516, 4327499, 54659460, 4392966,
      4328075, 4328320, 4327686, 3278854, 3278982, 4327814, 133761, 264577,
      3213318, 67457, 2164480, 52496010, 70321609, 70387338, 70387210, 27146783111,
      1696663696, 27164477325, 27182302861, 27182302604, 70387594, 1130498051, 104990601, 104990602,
      105056394, 6490886, 434917934035, 1698890882]
  | true, false, false, true =>
    stepsOf 6 [131841, 1696662530, 262145, 2162688, 69271940, 4391168, 4391563, 27163624839,
      27164476556, 27182367629, 1126237187, 4261382, 1126237315, 2164043, 69273220, 1126238096,
      1126237593, 1126237330, 69272970, 70387210, 70387209, 4327296, 4327430, 132993,
      2164480, 52496010, 70321609, 70387338, 70387210, 27146848647, 1696663696, 27164477325,
      27182302861, 27182302604, 70387594, 1130498051, 104990601, 104990602, 105056394, 6556422,
      434917934035, 1698890882]
  | true, false, true, false =>
    stepsOf 6 [66305, 1696662530, 131073, 2162688, 2163083, 4391168, 21168772, 27163493767,
      27164476556, 27182367629, 1126237187, 2164230, 1126237315, 2164043, 2164363, 2163974,
      1126238096, 1126237597, 1126237330, 1110508803, 4327040, 3278726, 4327558, 4392838,
      4327691, 54659076, 4327371, 21104132, 3278982, 4327814, 133761, 264577,
      3213318, 67457, 27146782599, 27181254285, 27182302604, 434917934035, 1698890882]
  | true, true, false, false =>
    stepsOf 6 [1696662530, 262145, 2162688, 69271940, 3277056, 70386308, 4391424, 4391819,
      70385993, 3277451, 6619648, 40174468, 27163625863, 27164477580, 1697777552, 27182368397,
      27182368140, 1698890898, 1680999683, 105055882, 105055754, 105055753, 6489984, 102828036,
      52496132, 1126237699, 52495754, 6555910, 6359558, 4262150, 3213318, 4393350,
      6490758, 199553, 52495626, 1126237827, 2164555, 69273732, 70387017, 3278411,
      70387588, 54658436, 4327051, 3278086, 18020174471, 1126238608, 1126238357, 1126238102,
      1126237595, 70387721, 3278720, 4327296, 6555782, 2164992, 102828036, 2164683,
      69273289, 27146849159, 1696664208, 1696663711, 27181254541, 27181254284, 69273546, 104925321,
      104925322, 1113655043, 104990922, 106039753, 1683097603, 6426315, 90311940, 6425611,
      23202564, 106039882, 1683097859, 5376128, 6621958, 6425606, 5376774, 5376902,
      6425734, 134529, 396417, 5507846, 434917934483, 1698890882]
  | true, true, true, true =>
    stepsOf 6 [132097, 66561, 2164102, 2163846, 1696663042, 262145, 3211264, 70320516,
      4391168, 4391563, 70320201, 3211659, 6619392, 23396996, 27163625351, 1697711760,
      27182302605, 27182302348, 1698890642, 1680933891, 105055626, 105055498, 105055497, 6489728,
      6555398, 6359046, 4261638, 3212806, 4392838, 6490246, 199041, 70321225,
      3212619, 70321796, 54592644, 4261259, 3212294, 18020173959, 1126238103, 1126237848,
      1126237342, 3278982, 4327814, 4393094, 4327947, 54659332, 4327627, 21104388,
      70387274, 21170052, 37947524, 4393291, 4393611, 4393856, 4393222, 3278982,
      4327814, 4393094, 4327947, 54659332, 4327627, 21104388, 70387337, 70387338,
      3279238, 4328070, 134017, 4393478, 199041, 21170052, 4393099, 4393344,
      198785, 6424838, 4327430, 2164614, 4262022, 6359430, 68225, 6555782,
      4326987, 104990596, 69272964, 102827652, 27146848647, 27181254797, 27181254540, 1698825625,
      1696663299, 69273226, 1698826243, 4327296, 434917934227, 1698890626]
  | _, _, _, _ => []

theorem chk323_0102 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0102 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0102 x y p q ++
        Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 1)) (S323_0102 x y p q) = true := by
  decide +kernel

theorem tag323_0102 : ∀ x y p q : Bool, ∀ g ∈ X323_0102 x y p q ++ Y323_0102 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,1}`, `{α,β} = {0,2}` (from `0`). -/
theorem rel323_0102 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw x a0 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw p a0 ++ negw q a1))) := by
  refine ⟨(X323_0102 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0102 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0102 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0102 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,1}`, `{α,β} = {1,3}`. -/
def X323_0113 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, false, false => [Gen.neg 2]
  | false, true, true, true => [Gen.x 0 2 (by decide), Gen.neg 0]
  | true, false, false, false => [Gen.neg 2]
  | true, false, true, true => [Gen.neg 0]
  | true, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,1}`, `{α,β} = {1,3}`. -/
def Y323_0113 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, false, true, false => [Gen.x 0 5 (by decide), Gen.x 1 4 (by decide), Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4, Gen.neg 5]
  | false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | false, true, true, true => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 5]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 5]
  | true, false, true, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 2, Gen.neg 3]
  | true, true, false, true => [Gen.x 0 5 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 4]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 4 5 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,1}`, `{α,β} = {1,3}`. -/
def S323_0113 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    stepsOf 6 [131585, 1696662274, 196609, 4325376, 54657412, 6619392, 56951428, 27181385095,
      1698825360, 1698825106, 6554752, 6489350, 4391942, 18020173447, 1126237338, 6424326,
      4326987, 104990596, 70321540, 103876228, 27181254797, 27182303116, 1698891161, 1697711875,
      70321802, 1698826243, 70387530, 434917934035, 1698890882]
  | false, false, true, false =>
    stepsOf 6 [66049, 1696662274, 196609, 4325376, 54657412, 6619392, 56951428, 27181385095,
      1698825360, 1698825106, 6554752, 6489350, 4391942, 18020173447, 1126237338, 6358790,
      1696663455, 27181254285, 27182302604, 1110509187, 103876489, 103876490, 1113654787, 1665271683,
      88213641, 88213642, 1666320131, 434917934035, 1698890882]
  | false, true, false, false =>
    stepsOf 6 [1696662274, 196609, 27181384071, 1126236826, 27181253773, 27182302092, 434917933523, 1698890370]
  | false, true, true, true =>
    stepsOf 6 [131841, 66305, 2163846, 2163590, 1696662786, 196609, 3211264, 3211659,
      27181384583, 434902205061, 3212171, 70321284, 1126237591, 1126237087, 4393094, 4393227,
      4393163, 37947140, 21169668, 4393478, 199041, 264577, 133249, 67457,
      70387017, 69272586, 52495689, 1110508547, 1696663184, 27181254029, 27182302348, 104990345,
      104990346, 434917933779, 1698890626]
  | true, false, false, false =>
    stepsOf 6 [1696662274, 196609, 27181384071, 3277318, 1126236827, 2163968, 52495498, 70321097,
      70386826, 70386698, 1696663184, 27164476813, 27182302349, 27182302092, 70387082, 1130497539,
      104990089, 104990090, 105055882, 434917933523, 1698890370]
  | true, false, true, true =>
    stepsOf 6 [131841, 66305, 2163846, 2163590, 1696662786, 65537, 27181252999, 1126236829,
      3278470, 4327302, 133249, 3212678, 4261510, 67457, 4392326, 27146782343,
      27146847623, 27181253773, 27182302092, 4392454, 434917933523, 1698890370]
  | true, true, false, true =>
    stepsOf 6 [132097, 1696662786, 196609, 4325376, 54657412, 6619392, 56951428, 27181385095,
      1698825360, 1698825106, 6554752, 6489350, 4391942, 6424070, 4326662, 3277830,
      6555398, 263809, 18020173447, 1126237339, 6424326, 2164480, 52496010, 2164875,
      102828420, 70321609, 70387338, 70387210, 1696664208, 1696663711, 27164477325, 27182302861,
      27182302604, 70387594, 1110509187, 70322122, 104925321, 104925322, 1130432259, 1113654787,
      70387466, 70387465, 104990922, 106039753, 1683097603, 87164809, 87164810, 87164682,
      87164681, 1683097731, 106039754, 23202436, 6425419, 90311812, 6621958, 6426315,
      6425984, 6425606, 5376774, 5376902, 6425734, 134529, 396417, 434917934035,
      1698890882]
  | true, true, true, false =>
    stepsOf 6 [66561, 1696662786, 196609, 3211264, 3211659, 4325632, 21103236, 6619648,
      23397252, 27181385607, 434902206085, 1698825616, 1698825362, 6555008, 103876100, 70321412,
      6489862, 4392454, 6424582, 4327174, 3278342, 6555910, 264321, 36767108,
      3212939, 2163974, 18020173959, 1126238103, 1126237597, 4393606, 4393739, 4393675,
      37947652, 21170180, 4393990, 199553, 265089, 2165126, 6359686, 68481,
      70387466, 3278923, 103942532, 4392779, 105056388, 70321796, 103876484, 27164478093,
      27182303629, 27182303372, 1698891417, 1697712131, 70322058, 1698892035, 4393088, 1697777667,
      434917934291, 1698891138]
  | _, _, _, _ => []

theorem chk323_0113 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0113 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0113 x y p q ++
        Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 1)) (S323_0113 x y p q) = true := by
  decide +kernel

theorem tag323_0113 : ∀ x y p q : Bool, ∀ g ∈ X323_0113 x y p q ++ Y323_0113 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,1}`, `{α,β} = {1,3}` (from `0`). -/
theorem rel323_0113 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw x a1 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw p a0 ++ negw q a1))) := by
  refine ⟨(X323_0113 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0113 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0113 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0113 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,2}`, `{α,β} = {0,1}`. -/
def X323_0201 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, true => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | false, true, false, true => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.neg 2]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.neg 0]
  | true, true, false, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,2}`, `{α,β} = {0,1}`. -/
def Y323_0201 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, false, true, true => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4]
  | false, true, false, true => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 1]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | true, true, false, false => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 3, Gen.neg 4]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,2}`, `{α,β} = {0,1}`. -/
def S323_0201 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    stepsOf 6 [1697710594, 196609, 2162688, 52494724, 4325632, 54657668, 69271625, 52494724,
      6619392, 56951428, 27146782599, 1696663184, 27181254029, 27181253772, 1698825106, 1679885315,
      104990090, 104989962, 104989961, 6424192, 6489862, 69272649, 2164107, 52496004,
      18020173959, 1126238096, 1126237598, 1126237336, 70386954, 70386953, 4327040, 52496132,
      2164427, 52495754, 4392971, 21169924, 4262150, 67713, 4327430, 4393222,
      264833, 54659332, 4327435, 70387530, 3278464, 4392710, 4327430, 3278598,
      264577, 3278726, 6424710, 4392523, 105056132, 70321540, 103876228, 27163494791,
      27182303373, 27182303116, 1698891161, 1697711875, 70321802, 1698891779, 4392832, 434917934035,
      1698890882]
  | false, false, true, true =>
    stepsOf 6 [197121, 66049, 3212166, 3211910, 1697711106, 196609, 2162688, 52494724,
      3277056, 3277451, 52494409, 2163083, 4391168, 21168772, 6619648, 23397252,
      27146783111, 1696663696, 27164477325, 27164477068, 27182368141, 1698825362, 105055626, 1679885827,
      1663108355, 1681000195, 103941770, 105056010, 1130498051, 104990538, 104990537, 6424192,
      6490374, 69272905, 1126237827, 2164619, 52496516, 70321418, 3212875, 3213195,
      3212806, 18020174471, 1126238608, 1126238359, 1126237854, 1126237586, 69273226, 21170308,
      37947780, 4393547, 4393867, 4394112, 4393478, 4393734, 199297, 264833,
      21104516, 4327499, 4327808, 4327430, 264577, 6490374, 2164614, 3213446,
      6359430, 68225, 3278726, 6424710, 3213568, 103876612, 3213259, 70321865,
      27163495303, 1697712784, 1697712287, 27182303117, 27182302860, 70322122, 104925321, 104925322,
      1130432259, 105056458, 106105289, 1683163139, 6491851, 90377476, 6491147, 23268100,
      106105418, 1683163395, 5441664, 6621958, 6491142, 5442310, 5442438, 6491270,
      200065, 396417, 5376774, 434917934291, 1698891138]
  | false, true, false, true =>
    stepsOf 6 [197377, 1697711106, 196609, 4325376, 54657412, 2163200, 52494596, 69271690,
      27146782087, 27181253773, 27181253516, 3278342, 69272649, 2164107, 52496004, 1126238096,
      1126237598, 1126237336, 70386954, 70386953, 4327040, 52496132, 2164427, 52495754,
      4392971, 21169924, 4262150, 67713, 4327430, 4393222, 264833, 54659332,
      4327435, 70387530, 3278464, 4392710, 4327430, 3278598, 264577, 198785,
      27163494279, 27182302861, 27182302604, 434917934035, 1698890882]
  | false, true, true, false =>
    stepsOf 6 [66305, 1697711106, 196609, 3276800, 3277195, 2163200, 2163147, 52494474,
      4391424, 21169028, 27146782599, 27164477069, 27164476812, 27182367885, 1126237443, 70387338,
      3278854, 69272905, 1126237827, 2164619, 52496516, 70321418, 3212875, 3213195,
      3212806, 1126238608, 1126238359, 1126237854, 1126237586, 69273226, 21170308, 37947780,
      4393547, 4393867, 4394112, 4393478, 4393734, 199297, 264833, 21104516,
      4327499, 4327808, 4327430, 264577, 2164742, 67457, 3212800, 70322057,
      27163494791, 1697712272, 27182303117, 27182302860, 105056393, 105056394, 6425350, 3279366,
      434917934291, 1698891138]
  | true, false, false, true =>
    stepsOf 6 [197377, 1697711106, 262145, 3276800, 70386052, 2163200, 69271812, 52494474,
      4391424, 4391819, 27146848135, 27164477069, 27164476812, 27182367885, 1126237443, 70387338,
      4261894, 69272905, 1126237827, 2164555, 69273732, 70321418, 36767364, 70322052,
      1126238608, 1126238359, 1126237849, 1126237586, 69273226, 4393088, 54658948, 4327563,
      3278598, 4327808, 3278854, 132993, 4392966, 198529, 3212800, 70322057,
      27163625863, 1697712272, 27182303117, 27182302860, 105056393, 105056394, 6556422, 434917934291,
      1698891138]
  | true, false, true, false =>
    stepsOf 6 [66305, 1697711106, 262145, 4325376, 4325771, 2163200, 2163147, 69271690,
      27146847623, 27181253773, 27181253516, 4261382, 69272649, 2164043, 69273220, 37815428,
      4261259, 2163718, 1126238096, 1126237848, 1126237341, 21104260, 4327243, 54659204,
      4327819, 4328064, 4392710, 4327430, 3278598, 4393094, 4393227, 4393163,
      37947140, 21169668, 3278982, 4327814, 4393094, 4327947, 54659332, 4327627,
      21104388, 70387274, 3279238, 4328070, 134017, 4393478, 199041, 70387402,
      21104516, 4327563, 4327808, 133249, 4261894, 67457, 27163625351, 27182302861,
      27182302604, 434917934035, 1698890882]
  | true, true, false, false =>
    stepsOf 6 [1697711106, 262145, 2162688, 69271940, 3277056, 70386308, 52494409, 69271940,
      4391168, 4391563, 6619648, 56951684, 27146848647, 1696663696, 27164477325, 27164477068,
      27182368141, 1698825362, 105055626, 1679885827, 1663108355, 1681000195, 103941770, 105056010,
      1130498051, 104990538, 104990537, 6424192, 6555910, 6359558, 4262150, 2164742,
      4327814, 6425222, 134017, 69272905, 1126237827, 2164555, 69273732, 70321418,
      36767364, 70322052, 18020174471, 1126238608, 1126238359, 1126237849, 1126237586, 69273226,
      4393088, 54658948, 4327563, 3278598, 4327808, 3278854, 132993, 6555782,
      3213568, 103876612, 3213259, 70321865, 27163626375, 1697712784, 1697712287, 27182303117,
      27182302860, 70322122, 104925321, 104925322, 1130432259, 105056458, 106105289, 1683163139,
      6491851, 90377476, 6491147, 23268100, 106105418, 1683163395, 5441664, 6621958,
      6491142, 5442310, 5442438, 6491270, 200065, 396417, 5507846, 434917934291,
      1698891138]
  | true, true, true, true =>
    stepsOf 6 [197633, 66561, 3212678, 3212422, 1697711618, 262145, 2162688, 69271940,
      4325632, 4326027, 69271625, 2163083, 6619392, 23396996, 27146848135, 1696663184,
      27181254029, 27181253772, 1698825106, 1679885315, 104990090, 104989962, 104989961, 6424192,
      6555398, 6359046, 4261638, 2164230, 4327302, 6424710, 133505, 69272649,
      2164043, 69273220, 37815428, 4261259, 2163718, 18020173959, 1126238096, 1126237848,
      1126237341, 21104260, 4327243, 54659204, 4327819, 4328064, 4392710, 4327430,
      3278598, 4393094, 4393227, 4393163, 37947140, 21169668, 3278982, 4327814,
      4393094, 4327947, 54659332, 4327627, 21104388, 70387274, 3279238, 4328070,
      134017, 4393478, 199041, 70387402, 21104516, 4327563, 4327808, 133249,
      6490374, 4392966, 3213190, 4262022, 6359430, 68225, 6555782, 4392523,
      105056132, 70321540, 103876228, 27163625863, 27182303373, 27182303116, 1698891161, 1697711875,
      70321802, 1698891779, 4392832, 434917934035, 1698890882]
  | _, _, _, _ => []

theorem chk323_0201 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 1) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0201 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0201 x y p q ++
        Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 2)) (S323_0201 x y p q) = true := by
  decide +kernel

theorem tag323_0201 : ∀ x y p q : Bool, ∀ g ∈ X323_0201 x y p q ++ Y323_0201 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,2}`, `{α,β} = {0,1}` (from `0`). -/
theorem rel323_0201 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw x a0 ++ negw y a1) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw p a0 ++ negw q a2))) := by
  refine ⟨(X323_0201 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0201 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0201 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0201 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,2}`, `{α,β} = {2,3}`. -/
def X323_0223 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, false => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | false, true, false, false => [Gen.neg 1]
  | false, true, true, true => [Gen.x 0 1 (by decide), Gen.neg 0]
  | true, false, false, false => [Gen.x 1 2 (by decide), Gen.neg 2]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.neg 0]
  | true, true, false, true => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,2}`, `{α,β} = {2,3}`. -/
def Y323_0223 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | false, false, true, false => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3, Gen.neg 4]
  | false, true, false, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | false, true, true, true => [Gen.x 0 1 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | true, false, true, true => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide)]
  | true, true, false, true => [Gen.x 0 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 4]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,2}`, `{α,β} = {2,3}`. -/
def S323_0223 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    stepsOf 6 [197121, 1697710850, 131073, 3276800, 3277131, 4325888, 54657284, 70385801,
      70385802, 6619648, 56951684, 27182368647, 27182368332, 1698825616, 1698825362, 6555008,
      103941636, 70386948, 6424326, 4326918, 3278155, 70387332, 18020173959, 1126238101,
      1126237594, 70387657, 6490374, 52495882, 1126238083, 52496516, 102828420, 4392779,
      105056388, 70387332, 103942020, 27164478092, 27182369165, 27182368908, 1698891417, 1697777667,
      70387594, 1698892035, 4393088, 1696663555, 69273482, 434917934291, 1698891138]
  | false, false, true, false =>
    stepsOf 6 [66049, 1697710850, 65537, 3276800, 20054404, 4325888, 21102852, 70385801,
      70385802, 6619648, 23397252, 27182303111, 27182368332, 1698825616, 1698825362, 6555008,
      103941636, 70386948, 6358790, 4261382, 18020173959, 1126237855, 1126237589, 843122179,
      3278720, 6359814, 4262406, 3213574, 2164742, 67457, 3278726, 4327558,
      6424966, 6555782, 3213568, 103876612, 3213259, 70321865, 27163495559, 27163626375,
      1697712784, 1697712287, 27182303117, 27182302860, 70322122, 104925321, 104925322, 1130432259,
      105056458, 106105289, 1683163139, 6491851, 90377476, 6491147, 23268100, 106105418,
      1683163395, 5441664, 6621958, 6491142, 5442310, 5442438, 6491270, 200065,
      396417, 5507846, 5377030, 4328198, 434917934291, 1698891138]
  | false, true, false, false =>
    stepsOf 6 [1697710850, 131073, 27182367111, 1126236825, 1126237059, 27164476556, 27182367629, 1126237187,
      434917933715, 1698890114]
  | false, true, true, true =>
    stepsOf 6 [197377, 66305, 3212422, 3212166, 1697711362, 131073, 2162688, 2163083,
      27182367623, 434917933701, 2163595, 69272708, 1126237584, 1126237087, 3278726, 4327558,
      4392838, 4327691, 54659076, 4327371, 21104132, 70387081, 70387082, 3278982,
      4327814, 133761, 264577, 198785, 67457, 69272586, 1126237571, 70386698,
      27164477068, 1697777040, 27182367885, 105055625, 105055626, 102828036, 52496132, 1679885827,
      1663108355, 434917933971, 1698890370]
  | true, false, false, false =>
    stepsOf 6 [1697710850, 131073, 3276800, 3277131, 27182367623, 27182367308, 3277643, 3277963,
      3277574, 1126237589, 1126237083, 3278208, 3212288, 70321545, 1697711760, 27182302605,
      27182302348, 105055881, 105055882, 434917933779, 1698890626]
  | true, false, true, true =>
    stepsOf 6 [197377, 66305, 3212422, 3212166, 1697711362, 131073, 2162688, 2163083,
      3277056, 20054660, 27182368135, 434917934213, 27182367564, 52495498, 52495370, 2164107,
      52496004, 1126238096, 1126237598, 1126237333, 52495754, 70387402, 21104516, 4327499,
      54659460, 4392966, 4328075, 4328320, 4327686, 3278854, 3278982, 4327814,
      133761, 264577, 198785, 67457, 27182302861, 27182302604, 434917934035, 1698890882]
  | true, true, false, true =>
    stepsOf 6 [197633, 1697711362, 131073, 3276800, 3277131, 4325888, 54657284, 70385801,
      70385802, 6619648, 56951684, 27182368647, 27182368332, 1698825616, 1698825362, 6555008,
      103941636, 70386948, 6424326, 4326918, 6490118, 4392710, 6555910, 264321,
      3278155, 3278475, 3278086, 18020173959, 1126238101, 1126237595, 3278720, 6489862,
      3213568, 103876612, 3213259, 70321865, 1697712784, 1697712287, 27182303117, 27182302860,
      70322122, 104925321, 104925322, 1130432259, 105056458, 106105289, 1683163139, 6491851,
      90377476, 6491147, 23268100, 106105418, 1683163395, 5441664, 6621958, 6491142,
      5442310, 5442438, 6491270, 200065, 396417, 434917934291, 1698891138]
  | true, true, true, false =>
    stepsOf 6 [66561, 1697711362, 131073, 2162688, 2163083, 3277056, 20054660, 4326144,
      21103108, 70386057, 70386058, 6619904, 23397508, 27182369159, 434917935237, 27182368588,
      1698825872, 1698825618, 6555264, 103941892, 70387204, 102828036, 69273348, 52496010,
      6424838, 4327430, 6490630, 4393222, 6556422, 264833, 52495882, 2164619,
      52496516, 18020174471, 1126238608, 1126238110, 1126237845, 52496266, 70387914, 21105028,
      4328011, 54659972, 4393478, 4328587, 4328832, 4328198, 3279366, 3279494,
      4328326, 134273, 265089, 3213702, 6359686, 68481, 4393035, 105056644,
      70322052, 103876740, 27182303885, 27182303628, 1698891673, 1697712387, 70322314, 1698892291,
      4393344, 434917934547, 1698891394]
  | _, _, _, _ => []

theorem chk323_0223 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw x 2 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0223 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0223 x y p q ++
        Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 2)) (S323_0223 x y p q) = true := by
  decide +kernel

theorem tag323_0223 : ∀ x y p q : Bool, ∀ g ∈ X323_0223 x y p q ++ Y323_0223 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,2}`, `{α,β} = {2,3}` (from `0`). -/
theorem rel323_0223 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a2 a3 c d h3 h4 h5 :: (negw x a2 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw p a0 ++ negw q a2))) := by
  refine ⟨(X323_0223 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0223 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0223 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0223 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,3}`, `{α,β} = {0,3}`. -/
def X323_0303 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, false, true => [Gen.x 0 1 (by decide), Gen.neg 2]
  | false, true, true, false => [Gen.x 0 1 (by decide), Gen.neg 0]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.neg 2]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.neg 0]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,3}`, `{α,β} = {0,3}`. -/
def Y323_0303 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, false, true, true => [Gen.x 0 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | false, true, false, true => [Gen.x 0 2 (by decide), Gen.neg 1]
  | false, true, true, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.neg 2]
  | true, true, false, false => [Gen.x 0 5 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,3}`, `{α,β} = {0,3}`. -/
def S323_0303 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    stepsOf 6 [1698759170, 196609, 2162688, 52494724, 4325632, 54657668, 6619648, 56951684,
      27180337031, 27181254284, 1698825616, 1698825362, 6555008, 102827524, 69272836, 6489862,
      4392454, 52495748, 69273220, 18020173959, 1126238096, 1126237594, 4327296, 4327302,
      6424710, 70321796, 103876484, 27180272007, 27182303372, 1698891417, 1697712131, 70322058,
      434917934291, 1698891138]
  | false, false, true, true =>
    stepsOf 6 [262657, 66049, 4260742, 4260486, 1698759682, 196609, 2162688, 52494724,
      4325632, 54657668, 6619648, 56951684, 27180337031, 27181254284, 1698825616, 1698825362,
      6555008, 102827524, 69272836, 6489862, 4392454, 52495748, 69273220, 18020173959,
      1126238096, 1126237594, 4327296, 6555910, 264321, 6359046, 2164486, 6424710,
      3212875, 103876484, 27180272007, 27182303372, 1698891423, 103877636, 87100164, 70322692,
      3213771, 1412499459, 103876490, 6425862, 5377030, 4328198, 434917934291, 1698891138]
  | false, true, false, true =>
    stepsOf 6 [262913, 1698759682, 196609, 2162688, 52494724, 27180336007, 27181253260, 52495236,
      69272708, 1126237584, 1126237082, 4326784, 263809, 27180270983, 27182302348, 434917933779,
      1698890626]
  | false, true, true, false =>
    stepsOf 6 [66305, 1698759682, 131073, 2162688, 2163083, 27180270471, 27181253260, 2163595,
      69272708, 1126237584, 1126237087, 3278726, 4327558, 4392838, 4327691, 54659076,
      4327371, 21104132, 70387081, 70387082, 3278982, 4327814, 133761, 264577,
      3213318, 67457, 69272586, 1126237571, 70386698, 27180337031, 27181254284, 27182368140,
      1698890896, 103941892, 70387204, 1680999683, 102828036, 69273348, 1679885827, 52495754,
      6490374, 4392966, 434917933779, 1698890626]
  | true, false, false, true =>
    stepsOf 6 [262913, 1698759682, 196609, 2162688, 52494724, 27180336007, 27181253260, 3212294,
      2163531, 52495492, 1126237584, 1126237083, 70387081, 70387082, 264321, 69272586,
      1126237571, 70386698, 27180271495, 27181254284, 27182368140, 1698890896, 103941892, 70387204,
      1680999683, 102828036, 69273348, 1679885827, 52495754, 6424838, 4327430, 434917933779,
      1698890626]
  | true, false, true, false =>
    stepsOf 6 [66305, 1698759682, 131073, 2162688, 2163083, 27180270471, 27181253260, 2163718,
      2163531, 2163851, 2163462, 1126237584, 1126237085, 21104004, 4326987, 54658948,
      4327563, 4327808, 4392454, 4327174, 3278342, 3278470, 4327302, 133249,
      264065, 3212806, 66945, 27180336519, 27182302348, 434917933779, 1698890626]
  | true, true, false, false =>
    stepsOf 6 [1698759682, 196609, 2162688, 52494724, 4325632, 54657668, 6619648, 56951684,
      27180337031, 27181254284, 1698825616, 1698825362, 6555008, 102827524, 69272836, 6489862,
      4392454, 6359046, 4261638, 3212806, 6555910, 264321, 2164043, 52496004,
      18020173959, 1126238096, 1126237595, 70387593, 70387594, 4327814, 6425222, 69273098,
      1126238083, 69273732, 102828420, 70387210, 70387588, 103942276, 4392587, 105056132,
      27180272519, 27181255308, 27182369164, 1698891920, 1698891423, 5507718, 6556550, 6621830,
      6556683, 90442500, 6556363, 56887556, 106170505, 106170506, 5507974, 6556806,
      265601, 396417, 87165700, 3279563, 1697777923, 1681000451, 103942026, 86051844,
      2165707, 1696664067, 1679886595, 1663109123, 102827914, 5377286, 434917934291, 1698891138]
  | true, true, true, true =>
    stepsOf 6 [263169, 66561, 4261254, 4260998, 1698760194, 131073, 2162688, 2163083,
      4325632, 21103236, 6619648, 23397252, 27180271495, 27181254284, 1698825616, 1698825362,
      6555008, 102827524, 69272836, 6424326, 4326918, 6359046, 4261638, 2164230,
      6555910, 264321, 2164043, 2164363, 2163974, 18020173959, 1126238096, 1126237597,
      21104516, 4327499, 54659460, 4328075, 4328320, 4392966, 4327686, 3278854,
      3278982, 4327814, 133761, 264577, 6555910, 3213190, 4262022, 6359430,
      68225, 4392838, 6490246, 70321796, 103876484, 27180337543, 27182303372, 1698891417,
      1697712131, 70322058, 434917934291, 1698891138]
  | _, _, _, _ => []

theorem chk323_0303 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0303 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0303 x y p q ++
        Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 3)) (S323_0303 x y p q) = true := by
  decide +kernel

theorem tag323_0303 : ∀ x y p q : Bool, ∀ g ∈ X323_0303 x y p q ++ Y323_0303 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,3}`, `{α,β} = {0,3}` (from `0`). -/
theorem rel323_0303 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw x a0 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw p a0 ++ negw q a3))) := by
  refine ⟨(X323_0303 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0303 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0303 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0303 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {0,3}`, `{α,β} = {1,2}`. -/
def X323_0312 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, false, true, false => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, false, false => [Gen.x 2 3 (by decide), Gen.neg 2]
  | false, true, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.neg 0]
  | true, false, false, false => [Gen.x 2 3 (by decide), Gen.neg 2]
  | true, false, true, true => [Gen.x 2 3 (by decide), Gen.neg 0]
  | true, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {0,3}`, `{α,β} = {1,2}`. -/
def Y323_0312 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, false, true, false => [Gen.x 0 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 0, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | false, true, false, false => [Gen.x 0 2 (by decide)]
  | false, true, true, true => [Gen.x 0 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, false, true, true => [Gen.x 0 2 (by decide), Gen.neg 1, Gen.neg 2]
  | true, true, false, true => [Gen.x 0 5 (by decide), Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 4]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {0,3}`, `{α,β} = {1,2}`. -/
def S323_0312 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    stepsOf 6 [262657, 1698759426, 262145, 3276800, 70386052, 4391168, 4391563, 6619648,
      56951684, 27164673927, 1697777296, 27182368141, 1698825362, 105055626, 105055498, 105055497,
      6489728, 6555398, 4392267, 4392587, 4392198, 18020173959, 1126238098, 1126237594,
      4327296, 6555398, 70321796, 103876484, 27182303372, 1698891417, 1697712131, 70322058,
      434917934291, 1698891138]
  | false, false, true, false =>
    stepsOf 6 [66049, 1698759426, 262145, 3276800, 70386052, 4391168, 4391563, 6619648,
      56951684, 27164673927, 1697777296, 27182368141, 1698825362, 105055626, 105055498, 105055497,
      6489728, 6555398, 4392267, 4392587, 4392198, 18020173959, 1126238098, 1126237594,
      4327296, 6358790, 3212875, 103876484, 27182303372, 1698891423, 103877636, 87100164,
      70322692, 3213771, 1412499459, 103876490, 434917934291, 1698891138]
  | false, true, false, false =>
    stepsOf 6 [1698759426, 262145, 4390912, 4391307, 27164672903, 27182367373, 4391942, 4391755,
      4392075, 4391686, 1126237586, 1126237082, 4326784, 27182302348, 434917933779, 1698890626]
  | false, true, true, true =>
    stepsOf 6 [262913, 66305, 4260998, 4260742, 1698759938, 262145, 4259840, 4260235,
      4391168, 21168772, 27164673415, 434634818693, 27182367629, 70321226, 4392454, 70321225,
      3212683, 70321796, 4260939, 4261259, 4260870, 1126238103, 1126237848, 1126237343,
      3278982, 4327814, 4393094, 4327947, 54659332, 4327627, 21104388, 70387337,
      70387338, 21170052, 37947524, 4393291, 4393611, 4393856, 4393222, 21104260,
      4327243, 54659204, 4327819, 4328064, 4392710, 4327430, 3278598, 3278726,
      4327558, 133505, 4392966, 198529, 4392907, 21169668, 198785, 264321,
      67457, 70321418, 27182302860, 1698891152, 103876612, 70321924, 1680934403, 434917934035,
      1698890882]
  | true, false, false, false =>
    stepsOf 6 [1698759426, 262145, 4390912, 4391307, 27164672903, 27182367373, 4326406, 1126237337,
      1126237074, 69272714, 69272586, 1126237571, 70386698, 27181254284, 27182368140, 1698890896,
      103941892, 70387204, 1680999683, 102828036, 69273348, 1679885827, 52495754, 434917933779,
      1698890626]
  | true, false, true, true =>
    stepsOf 6 [262913, 66305, 4260998, 4260742, 1698759938, 65537, 4390912, 21168516,
      27164476295, 27182367373, 1126237341, 1126237074, 1110508547, 4326784, 264321, 2164102,
      3212934, 67457, 3278214, 27180271239, 27180336519, 27182302348, 3278342, 434917933779,
      1698890626]
  | true, true, false, true =>
    stepsOf 6 [263169, 1698759938, 262145, 3276800, 70386052, 4391168, 4391563, 70385737,
      3277195, 6619392, 40174212, 27164673927, 1697777296, 27182368141, 27182367884, 1698890642,
      1680999427, 105055626, 105055498, 105055497, 6489728, 6555398, 6424582, 4327174,
      3278342, 4392838, 6490246, 199041, 70386761, 3278155, 70387332, 54658180,
      4326795, 3277830, 18020173959, 1126238101, 1126237846, 1126237339, 70387465, 3278464,
      6555398, 69272842, 69273220, 102827908, 4326795, 104990340, 27181254796, 1698826128,
      1698825631, 5507462, 6556294, 6621574, 6556427, 90442244, 6556107, 40110084,
      106170249, 106170250, 5507718, 6556550, 265345, 396161, 86051332, 2165195,
      1696663555, 1679886083, 102827658, 434917934227, 1698890626]
  | true, true, true, false =>
    stepsOf 6 [66561, 1698759938, 262145, 2162688, 69271940, 3211776, 70320388, 52494473,
      52494474, 4391424, 4391819, 70386122, 70320201, 1110507907, 3211915, 6619648,
      23397252, 27164674439, 27164477516, 1697712016, 27182302861, 27182302604, 1698890898, 1680934147,
      105055882, 105055754, 105055753, 6489984, 102828036, 52496132, 1126237699, 52495817,
      6555910, 6425094, 4327686, 3278854, 4393350, 6490758, 199553, 52495689,
      1126237827, 2164619, 69273732, 70321481, 3212875, 70322052, 54592900, 4261515,
      3212550, 18020174471, 1126238608, 1126238359, 1126238104, 1126237598, 3279238, 4328070,
      4393350, 4328203, 54659588, 4327883, 21104644, 70387530, 21170308, 37947780,
      4393547, 4393867, 4394112, 4393478, 3279238, 4328070, 4393350, 4328203,
      54659588, 4327883, 21104644, 70387593, 70387594, 3279494, 4328326, 134273,
      4393734, 199297, 21170308, 4393355, 4393600, 199041, 21104516, 4327563,
      4327808, 133249, 4261766, 6359174, 67969, 69273220, 102827908, 27181254796,
      1698825881, 1696663555, 69273482, 434917934483, 1698890882]
  | _, _, _, _ => []

theorem chk323_0312 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_0312 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_0312 x y p q ++
        Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw p 0 ++ negw q 3)) (S323_0312 x y p q) = true := by
  decide +kernel

theorem tag323_0312 : ∀ x y p q : Bool, ∀ g ∈ X323_0312 x y p q ++ Y323_0312 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {0,3}`, `{α,β} = {1,2}` (from `0`). -/
theorem rel323_0312 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw x a1 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw p a0 ++ negw q a3))) := by
  refine ⟨(X323_0312 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_0312 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_0312 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_0312 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,2}`, `{α,β} = {0,3}`. -/
def X323_1203 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 2 (by decide)]
  | false, false, true, false => [Gen.x 0 1 (by decide)]
  | false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 2]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, true => [Gen.x 0 2 (by decide)]
  | true, true, true, false => [Gen.x 0 1 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,2}`, `{α,β} = {0,3}`. -/
def Y323_1203 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 2 3 (by decide), Gen.neg 3]
  | false, false, true, false => [Gen.x 1 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | false, true, false, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | false, true, true, true => [Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 4]
  | true, false, false, false => [Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 4]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 3]
  | true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.neg 3]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,2}`, `{α,β} = {0,3}`. -/
def S323_1203 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    stepsOf 6 [197121, 1697776386, 3211264, 27182301580, 1126236823, 4392198, 197761, 27164673159,
      27182367629, 434917933715, 1698890114]
  | false, false, true, false =>
    stepsOf 6 [131585, 1697776386, 2162688, 27181253004, 1126236816, 4326662, 132225, 3277568,
      70386825, 27164673671, 1697777040, 27182367885, 27182367628, 105055625, 105055626, 6555654,
      434917933523, 1698890370]
  | false, true, false, false =>
    stepsOf 6 [1697776386, 2162688, 3211520, 52494473, 52494474, 4325888, 70386057, 70386058,
      6619904, 27181254540, 434902206085, 1698825616, 1698825362, 6555008, 103876100, 70321412,
      102827780, 69273092, 52495817, 6555654, 264065, 52495689, 18020173703, 1126237840,
      1126237591, 4392838, 54659076, 4327371, 70387274, 3279110, 133249, 6556038,
      4392779, 105056388, 70387332, 103942020, 27164674695, 27182369165, 27182368908, 1698891417,
      1697777667, 70387594, 1698892035, 4393088, 434917934291, 1698891138]
  | false, true, true, true =>
    stepsOf 6 [197377, 131841, 3277958, 3277702, 1697776898, 2162688, 4325632, 6619648,
      27181254028, 1698825360, 1698825106, 6554752, 102827268, 69272580, 6555142, 263553,
      18020173191, 1126237328, 6490118, 4392710, 3278470, 4327302, 6424710, 133505,
      6555526, 3278848, 103941892, 3278539, 70387145, 27164674695, 1697778064, 1697777567,
      27182368397, 27182368140, 70387402, 104990601, 104990602, 1130497539, 105056202, 106105033,
      1683162883, 6491595, 90377220, 6490891, 40045060, 106105162, 1683163139, 5441408,
      6621702, 6490886, 5442054, 5442182, 6491014, 199809, 396161, 5507590,
      434917934035, 1698890882]
  | true, false, false, false =>
    stepsOf 6 [1697776386, 131073, 196865, 2163200, 52494596, 2162891, 4326144, 54657540,
      21102852, 6620160, 56951556, 23396868, 27180272007, 27180337287, 27181254540, 1698825872,
      1698825618, 6555264, 102827780, 69273092, 6490118, 4392710, 6424838, 4327430,
      3278598, 6359558, 4262150, 3213318, 2164486, 2164299, 2164619, 52496516,
      69273988, 2164230, 3278726, 4327558, 3212934, 4261766, 18020174727, 1126238864,
      1126238365, 1126237850, 1110509571, 3213184, 4327296, 3278982, 4327814, 4393094,
      4327947, 54659332, 4327627, 21104388, 3279238, 4328070, 134017, 264833,
      3213446, 6359430, 3279360, 103942404, 3279051, 70387657, 27164478599, 1697778576,
      1697778079, 27182368909, 27182368652, 70387914, 104991113, 104991114, 1130498051, 105056714,
      106105545, 1683163395, 6492107, 90377732, 6491403, 40045572, 106105674, 1683163651,
      5441920, 6622214, 6491398, 5442566, 5442694, 6491526, 200321, 396673,
      5311494, 2165510, 434917934547, 1698891394]
  | true, false, true, true =>
    stepsOf 6 [197377, 131841, 3277958, 3277702, 1697776898, 2162688, 4325632, 6619648,
      27181254028, 1698825360, 1698825106, 6554752, 102827268, 69272580, 6358534, 4261126,
      2163787, 69272964, 18020173703, 1126237840, 1126237337, 70387274, 6490630, 4393222,
      3278982, 4327814, 6425222, 134017, 6556038, 52495689, 1126237827, 52496260,
      102828164, 4392523, 105056132, 70321540, 103876228, 27164674695, 27164477772, 27182303373,
      27182303116, 1698891161, 1697711875, 70321802, 1698891779, 4392832, 1696663299, 69273289,
      434917934035, 1698890882]
  | true, true, false, true =>
    stepsOf 6 [197633, 1697776898, 3211264, 27182301580, 3211851, 70321028, 1126237335, 1126236826,
      4392710, 198273, 1110508419, 70321354, 70386442, 27164673671, 434634818949, 1697776784,
      27182367629, 105055369, 105055370, 104924932, 54593028, 104924554, 103875658, 6555654,
      434917933715, 1698890114]
  | true, true, true, false =>
    stepsOf 6 [132097, 1697776898, 2162688, 27181253004, 2163275, 69272452, 1126237328, 1126236825,
      70386762, 4327174, 132737, 52495177, 1126237315, 27164673671, 27164476748, 27182302349,
      27182302092, 1126237443, 52495561, 434917933523, 1698890370]
  | _, _, _, _ => []

theorem chk323_1203 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 0 3 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1203 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1203 x y p q ++
        Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 2)) (S323_1203 x y p q) = true := by
  decide +kernel

theorem tag323_1203 : ∀ x y p q : Bool, ∀ g ∈ X323_1203 x y p q ++ Y323_1203 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,2}`, `{α,β} = {0,3}` (from `0`). -/
theorem rel323_1203 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a3 c d (h1.trans (h2.trans h3)) h4 h5 :: (negw x a0 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw p a1 ++ negw q a2))) := by
  refine ⟨(X323_1203 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1203 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1203 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1203 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,2}`, `{α,β} = {1,2}`. -/
def X323_1212 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 2 3 (by decide)]
  | false, false, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide)]
  | false, true, false, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 1 5 (by decide), Gen.x 2 3 (by decide), Gen.x 3 4 (by decide)]
  | true, true, false, false => [Gen.x 2 3 (by decide)]
  | true, true, true, true => [Gen.x 0 3 (by decide), Gen.x 2 3 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,2}`, `{α,β} = {1,2}`. -/
def Y323_1212 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => [Gen.x 1 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | false, false, true, true => [Gen.x 1 2 (by decide), Gen.x 2 3 (by decide)]
  | false, true, false, true => [Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 4]
  | false, true, true, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4, Gen.neg 5]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide)]
  | true, true, true, true => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 5]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,2}`, `{α,β} = {1,2}`. -/
def S323_1212 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    stepsOf 6 [1697776130, 4390912, 27182367117, 1126236818, 3277568, 70386825, 1697777040, 27182367885,
      27182367628, 105055625, 105055626, 434917933523, 1698890370]
  | false, false, true, true =>
    stepsOf 6 [197121, 131585, 3277702, 3277446, 1697776642, 4259840, 4391168, 434634818437,
      27182367373, 70320970, 70320969, 1126237335, 1126237080, 70386698, 70386697, 4326784,
      4392459, 37946628, 4392710, 264321, 198529, 132737, 27182368141, 27182367884,
      434917933779, 1698890626]
  | false, true, false, true =>
    stepsOf 6 [197377, 1697776642, 3276800, 4391168, 6619648, 1697777040, 27182367885, 1698825106,
      105055370, 105055242, 105055241, 6489472, 6489606, 198017, 18020173191, 1126237330,
      6489606, 3278848, 103941892, 3278539, 70387145, 1697778064, 1697777567, 27182368397,
      27182368140, 70387402, 104990601, 104990602, 1130497539, 105056202, 106105033, 1683162883,
      6491595, 90377220, 6490891, 40045060, 106105162, 1683163139, 5441408, 6621702,
      6490886, 5442054, 5442182, 6491014, 199809, 396161, 434917934035, 1698890882]
  | false, true, true, false =>
    stepsOf 6 [131841, 1697776642, 4259840, 3277056, 4391424, 6619904, 434634819461, 1697777296,
      27182368141, 1698825362, 105055626, 105055498, 105055497, 6489728, 104924932, 54593028,
      70321482, 6490118, 198529, 70321481, 18020173703, 1126237847, 1126237592, 70387210,
      70387209, 4327296, 4392971, 37947140, 4393222, 264833, 3278982, 6424966,
      133761, 4392779, 105056388, 70387332, 103942020, 27182369165, 27182368908, 1698891417,
      1697777667, 70387594, 1698892035, 4393088, 434917934291, 1698891138]
  | true, false, false, true =>
    stepsOf 6 [197377, 1697776642, 3276800, 4391168, 6619648, 1697777040, 27182367885, 1698825106,
      105055370, 105055242, 105055241, 6489472, 6424070, 3278086, 18020173703, 1126237595,
      1126237330, 69272906, 70387401, 6490118, 52495689, 1126237827, 52496260, 102828164,
      4392523, 105056132, 70321540, 103876228, 27164477772, 27182303373, 27182303116, 1698891161,
      1697711875, 70321802, 1698891779, 4392832, 1696663299, 69273289, 434917934035, 1698890882]
  | true, false, true, false =>
    stepsOf 6 [131841, 1697776642, 6422528, 4391168, 5505536, 1697777048, 27182367885, 1698825109,
      88278154, 1415775491, 106103945, 106103946, 106169738, 6620800, 105055242, 105055241,
      6489472, 5375494, 3278086, 18020108167, 1126237595, 1126237330, 69272906, 70387401,
      5376006, 52495689, 1126237827, 2164619, 86050948, 27164477772, 1697712030, 27182302861,
      27182302604, 70321929, 3212928, 102828804, 86051332, 52496644, 2164747, 1696663299,
      69273289, 434917934035, 1698890882]
  | true, true, false, false =>
    stepsOf 6 [1697776642, 4390912, 27182367117, 1126237083, 1126236818, 69272394, 70386889, 52495177,
      1126237315, 27164476748, 27182302349, 27182302092, 1126237443, 52495561, 434917933523, 1698890370]
  | true, true, true, true =>
    stepsOf 6 [197633, 132097, 3278214, 3277958, 1697777154, 4259840, 4391168, 434634818437,
      27182367373, 70320970, 70320969, 36766852, 3212683, 2163718, 1126237847, 1126237341,
      1126237080, 70386698, 70386697, 4326784, 3278214, 36767236, 3212747, 52495434,
      4327179, 21104132, 70387081, 70387082, 4261894, 67457, 4327174, 4392966,
      264577, 37947012, 4392779, 4393088, 4392710, 264321, 198529, 132737,
      69272649, 3212288, 70321545, 27164477260, 1697711760, 27182302605, 27182302348, 105055881,
      105055882, 102828292, 52496388, 1679886083, 1663108611, 52495817, 434917933779, 1698890626]
  | _, _, _, _ => []

theorem chk323_1212 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1212 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1212 x y p q ++
        Gen.k 1 2 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 2)) (S323_1212 x y p q) = true := by
  decide +kernel

theorem tag323_1212 : ∀ x y p q : Bool, ∀ g ∈ X323_1212 x y p q ++ Y323_1212 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,2}`, `{α,β} = {1,2}` (from `0`). -/
theorem rel323_1212 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw x a1 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a2 c d h2 (h3.trans h4) h5 :: (negw p a1 ++ negw q a2))) := by
  refine ⟨(X323_1212 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1212 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1212 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1212 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,3}`, `{α,β} = {0,1}`. -/
def X323_1301 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | false, false, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide)]
  | false, true, false, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, false => [Gen.x 0 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, true => [Gen.x 0 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)]
  | true, true, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,3}`, `{α,β} = {0,1}`. -/
def Y323_1301 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.neg 2]
  | false, false, true, false => [Gen.x 1 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | false, true, false, false => [Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | false, true, true, true => [Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 5 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 2]
  | true, true, false, true => [Gen.x 0 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 5]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.neg 2]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,3}`, `{α,β} = {0,1}`. -/
def S323_1301 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    stepsOf 6 [262657, 1698824962, 4325376, 3211264, 1110507907, 27181253517, 27182301836, 1110508419,
      1126237335, 1126237078, 4392064, 263553, 27181384839, 434917933971, 1698890370]
  | false, false, true, false =>
    stepsOf 6 [131585, 1698824962, 4325376, 2162944, 69271690, 27181253517, 27181253260, 69272393,
      1126237328, 1126237080, 70386698, 70386697, 4326784, 3278214, 4326923, 54658308,
      70386825, 70386826, 4327174, 3278342, 264321, 3278598, 132737, 70386698,
      27181385351, 27182368140, 1698890896, 103941892, 70387204, 1680999683, 6490118, 4392710,
      434917933779, 1698890626]
  | false, true, false, false =>
    stepsOf 6 [1698824962, 2162688, 3277056, 52494409, 4391168, 6619648, 1696663440, 27164477069,
      27164476812, 27182367885, 1698825106, 105055370, 1679885571, 1663108099, 1680999939, 103941514,
      105055754, 1130497795, 104990282, 104990281, 6423936, 6424582, 132993, 69272649,
      1126237571, 70321162, 18020173703, 1126237840, 1126237591, 1126237330, 4327627, 54658820,
      70387274, 70387273, 4326784, 3278342, 3278598, 132737, 4392582, 6489990,
      70387076, 103941764, 27181385863, 27182368652, 1698891161, 1697777411, 70387338, 434917934035,
      1698890882]
  | false, true, true, true =>
    stepsOf 6 [262913, 131841, 4326534, 4326278, 1698825474, 2162688, 4325632, 69271625,
      6619392, 1696662928, 27181253773, 27181253516, 1698824850, 1679885059, 104989834, 104989706,
      104989705, 6423936, 6424070, 132481, 69272393, 18020173191, 1126237328, 1126237080,
      70386698, 70386697, 4326784, 3278214, 4326923, 54658308, 70386825, 70386826,
      4327174, 3278342, 264321, 6555654, 3278470, 4327302, 6424710, 133505,
      4392582, 6489990, 70386698, 70387076, 103941764, 4392075, 105055620, 27181385863,
      27182368652, 1698891408, 1698890911, 5507206, 6556038, 6621318, 6556171, 90441988,
      6555851, 56887044, 106169993, 106169994, 5507462, 6556294, 265089, 395905,
      87165188, 3279051, 1697777411, 1680999939, 103941514, 5442054, 434917933779, 1698890626]
  | true, false, false, false =>
    stepsOf 6 [1698824962, 2162688, 3277056, 52494409, 4391168, 6619648, 1696663440, 27164477069,
      27164476812, 27182367885, 1698825106, 105055370, 1679885571, 1663108099, 1680999939, 103941514,
      105055754, 1130497795, 104990282, 104990281, 6423936, 6359046, 2164486, 69272649,
      1126237571, 2164299, 2164619, 2164230, 70321162, 18020174215, 1126238352, 1126237853,
      1126237591, 1126237330, 70322180, 3213259, 70321802, 69272906, 4327883, 21104644,
      70387530, 70387529, 4327040, 2164742, 67457, 132993, 4392838, 54659076,
      4327371, 70387337, 70387338, 3279110, 133249, 4393094, 6490502, 69272905,
      1126237827, 69273476, 102828164, 70321418, 70321796, 103876484, 4392331, 105055876,
      27181386375, 27181254988, 27182303372, 1698891664, 1698891167, 5507462, 6556294, 6621574,
      6556427, 90442244, 6556107, 56887300, 106170249, 106170250, 5507718, 6556550,
      265345, 396161, 87099908, 3213771, 1697712131, 1680934659, 103876234, 86051588,
      2165259, 1696663811, 1679886339, 1663108867, 102827721, 5442566, 434917934035, 1698890882]
  | true, false, true, true =>
    stepsOf 6 [262913, 131841, 4326534, 4326278, 1698825474, 2162688, 4325632, 69271625,
      6619392, 1696662928, 27181253773, 27181253516, 1698824850, 1679885059, 104989834, 104989706,
      104989705, 6423936, 6358534, 2163974, 69272393, 2163787, 2164107, 2163718,
      18020173703, 1126237840, 1126237341, 1126237080, 70386698, 70386697, 4326784, 3278214,
      36767236, 3212747, 52495434, 4327179, 21104132, 70387081, 70387082, 4261894,
      67457, 4327174, 4392966, 264577, 70386954, 70386953, 4326987, 54658948,
      4327552, 4392454, 4327174, 3278342, 264321, 6555654, 3278470, 4327302,
      6424710, 133505, 4392582, 6489990, 52495433, 69272964, 102827652, 70321284,
      103875972, 27181385863, 27181254476, 27182302860, 1698890905, 1697711619, 70321546, 1696663299,
      1126237699, 69273033, 434917933779, 1698890626]
  | true, true, false, true =>
    stepsOf 6 [263169, 1698825474, 4325376, 3211264, 1110507907, 27181253517, 27182301836, 1110508419,
      1126237597, 1126237335, 1126237078, 4392064, 70321412, 3212491, 4327115, 21103876,
      2164486, 67201, 132737, 264065, 1110508675, 27181385351, 434902205829, 1698825360,
      103876356, 70321668, 1680934147, 6490118, 4392710, 434917933971, 1698890370]
  | true, true, true, false =>
    stepsOf 6 [132097, 1698825474, 4325376, 2162944, 69271690, 27181253517, 27181253260, 69272393,
      2163787, 2164107, 2163718, 1126237840, 1126237341, 1126237080, 70386698, 70386697,
      4326784, 3278214, 36767236, 3212747, 52495434, 4327179, 21104132, 70387081,
      70387082, 4261894, 67457, 4327174, 4392966, 264577, 70386954, 70386953,
      4326987, 54658948, 4327552, 4392454, 4327174, 3278342, 264321, 3278598,
      132737, 52495433, 27181385351, 27181253964, 27182302348, 52495817, 434917933779, 1698890626]
  | _, _, _, _ => []

theorem chk323_1301 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 0 1 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 1) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1301 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1301 x y p q ++
        Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 3)) (S323_1301 x y p q) = true := by
  decide +kernel

theorem tag323_1301 : ∀ x y p q : Bool, ∀ g ∈ X323_1301 x y p q ++ Y323_1301 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,3}`, `{α,β} = {0,1}` (from `0`). -/
theorem rel323_1301 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a1 c d h1 (h2.trans (h3.trans h4)) h5 :: (negw x a0 ++ negw y a1) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw p a1 ++ negw q a3))) := by
  refine ⟨(X323_1301 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1301 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1301 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1301 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {1,3}`, `{α,β} = {2,3}`. -/
def X323_1323 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 0 1 (by decide)]
  | false, true, false, true => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => []
  | true, true, true, true => [Gen.x 0 1 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {1,3}`, `{α,β} = {2,3}`. -/
def Y323_1323 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | false, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 1 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 2 (by decide), Gen.x 1 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 4]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => [Gen.x 0 2 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, true, true, true => [Gen.x 0 2 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {1,3}`, `{α,β} = {2,3}`. -/
def S323_1323 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    stepsOf 6 [1698824706, 434917933459, 1698889858]
  | false, false, true, true =>
    stepsOf 6 [262657, 131585, 4326278, 4326022, 1698825218, 2162688, 434917933445, 1126236816,
      263553, 132225, 1698825104, 434917933715, 1698890114]
  | false, true, false, true =>
    stepsOf 6 [262913, 1698825218, 4390912, 6619392, 1698890640, 1698890386, 6554496, 6554630,
      263041, 18020172679, 6554630, 1698825369, 434917933971, 1698890370]
  | false, true, true, false =>
    stepsOf 6 [131841, 1698825218, 4390912, 6619392, 1698890640, 1698890386, 6554496, 6554630,
      263041, 18020172679, 6423558, 1698825375, 434917933971, 1698890370]
  | true, false, false, true =>
    stepsOf 6 [262913, 1698825218, 4390912, 6619392, 1698890640, 1698890386, 6554496, 6489094,
      4391686, 18020173191, 1126237082, 6555142, 1110508675, 70321540, 103876228, 4326539,
      104990084, 434902206341, 1698825872, 1698825375, 5507206, 6556038, 6621318, 6556171,
      90441988, 6555851, 40109828, 106169993, 106169994, 5507462, 6556294, 265089,
      395905, 87099652, 36767748, 1697711875, 1680934403, 1647379715, 434917933971, 1698890370]
  | true, false, true, false =>
    stepsOf 6 [131841, 1698825218, 2162688, 4391168, 6619648, 434917934469, 1698890896, 1698890642,
      6554752, 102827268, 69272580, 6489606, 4392198, 52495492, 69272964, 18020173703,
      1126237840, 1126237338, 4327040, 4327046, 6424454, 133249, 70321540, 103876228,
      434902206341, 1698825625, 1697711875, 1110509059, 434917934227, 1698890626]
  | true, true, false, false =>
    stepsOf 6 [1698825218, 1126236570, 1110508163, 434902205317, 1698824848, 103875844, 70321156, 1680933635,
      434917933459, 1698889858]
  | true, true, true, true =>
    stepsOf 6 [263169, 132097, 4326790, 4326534, 1698825730, 2162688, 434917933445, 52494980,
      69272452, 1126237328, 1126236826, 4326528, 263553, 132225, 434902205317, 434917933715,
      1698890114]
  | _, _, _, _ => []

theorem chk323_1323 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw x 2 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_1323 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_1323 x y p q ++
        Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw p 1 ++ negw q 3)) (S323_1323 x y p q) = true := by
  decide +kernel

theorem tag323_1323 : ∀ x y p q : Bool, ∀ g ∈ X323_1323 x y p q ++ Y323_1323 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {1,3}`, `{α,β} = {2,3}` (from `0`). -/
theorem rel323_1323 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a2 a3 c d h3 h4 h5 :: (negw x a2 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw p a1 ++ negw q a3))) := by
  refine ⟨(X323_1323 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_1323 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_1323 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_1323 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {2,3}`, `{α,β} = {0,2}`. -/
def X323_2302 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | false, false, true, false => [Gen.x 0 3 (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide)]
  | false, true, false, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 1 2 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, true => [Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)]
  | true, true, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 2]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {2,3}`, `{α,β} = {0,2}`. -/
def Y323_2302 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, true => [Gen.neg 1]
  | false, false, true, false => [Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | false, true, false, false => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | false, true, true, true => [Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, false, false => [Gen.x 0 1 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 1, Gen.neg 2, Gen.neg 4]
  | true, false, true, true => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide), Gen.neg 1]
  | true, true, false, true => [Gen.x 0 1 (by decide), Gen.x 3 5 (by decide), Gen.neg 1, Gen.neg 3, Gen.neg 5]
  | true, true, true, false => [Gen.neg 0]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {2,3}`, `{α,β} = {0,2}`. -/
def S323_2302 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, true =>
    stepsOf 6 [262657, 1698890498, 2162688, 4391168, 27164476300, 27182367373, 1126236931, 1126237059,
      1126237328, 1126237074, 4326528, 263553, 27182367879, 434917933779, 1698890626]
  | false, false, true, false =>
    stepsOf 6 [197121, 1698890498, 2162688, 4260096, 69271689, 69271690, 4391424, 27164476812,
      434634818693, 27182367629, 70321226, 1126237443, 52495561, 52495433, 1126237571, 70321225,
      1126237840, 1126237591, 1126237336, 70386954, 70386953, 4327040, 4392715, 37946884,
      4392966, 264577, 70387146, 4326987, 54658948, 4392454, 4327552, 4327174,
      3278342, 264321, 198529, 27182368391, 1698891152, 6424582, 4327174, 434917934035,
      1698890882]
  | false, true, false, false =>
    stepsOf 6 [1698890498, 2162688, 3277056, 4391424, 6619904, 27164477324, 1697777296, 27182368141,
      1698825362, 105055626, 105055498, 105055497, 6489728, 102827780, 52495876, 1126237443,
      6490118, 198529, 1126237571, 18020173703, 1126237840, 1126237586, 4327040, 4327046,
      6424454, 27182368903, 1698891417, 434917934291, 1698891138]
  | false, true, true, true =>
    stepsOf 6 [262913, 197377, 4392070, 4391814, 1698891010, 2162688, 4260096, 69271689,
      69271690, 3277056, 70386313, 6619648, 27164477324, 434634819205, 1697777040, 27182367885,
      1698825106, 105055370, 105055242, 105055241, 6489472, 104924676, 54592772, 70321226,
      102827780, 52495876, 1126237443, 52495561, 6490118, 198529, 52495433, 1126237571,
      70321225, 18020173703, 1126237840, 1126237591, 1126237336, 70386954, 70386953, 4327040,
      4392715, 37946884, 4392966, 264577, 70387146, 4326987, 54658948, 4392454,
      4327552, 4327174, 3278342, 264321, 6555654, 4392838, 6490246, 199041,
      4327046, 6424454, 4392331, 105055876, 27182368903, 1698891664, 1698891167, 5507462,
      6556294, 6621574, 6556427, 90442244, 6556107, 56887300, 106170249, 106170250,
      5507718, 6556550, 265345, 396161, 5376518, 3279110, 434917934035, 1698890882]
  | true, false, false, false =>
    stepsOf 6 [1698890498, 2162688, 3277056, 4391424, 6619904, 27164477324, 1697777296, 27182368141,
      1698825362, 105055626, 105055498, 105055497, 6489728, 102827780, 52495876, 1126237443,
      6359046, 3213062, 1126237571, 2164299, 52496260, 18020174215, 1126238352, 1126237851,
      1126237586, 69273162, 70387657, 70387786, 3278720, 4327558, 6424966, 1126237827,
      69273476, 102828164, 4392587, 105056132, 27182369415, 434917935493, 1698891920, 1698891423,
      5507718, 6556550, 6621830, 6556683, 90442500, 6556363, 56887556, 106170505,
      106170506, 5507974, 6556806, 265601, 396417, 86051588, 52496900, 1696663811,
      1679886339, 1663108867, 5377030, 3279622, 434917934291, 1698891138]
  | true, false, true, true =>
    stepsOf 6 [262913, 197377, 4392070, 4391814, 1698891010, 2162688, 4260096, 69271689,
      69271690, 3277056, 70386313, 6619648, 27164477324, 434634819205, 1697777040, 27182367885,
      1698825106, 105055370, 105055242, 105055241, 6489472, 104924676, 54592772, 70321226,
      102827780, 52495876, 1126237443, 52495561, 6359046, 3213062, 52495433, 1126237571,
      2164299, 52496260, 70321225, 36767108, 3212939, 2163974, 18020174215, 1126238352,
      1126238103, 1126237597, 1126237336, 70386954, 70386953, 4327040, 3278470, 36767492,
      3213003, 52495690, 4327435, 21104388, 70387337, 70387338, 4262150, 67713,
      4327430, 4393222, 264833, 37947268, 4393035, 4393344, 4392966, 264577,
      4326987, 54658948, 4392454, 4327552, 4327174, 3278342, 264321, 6555654,
      4392838, 6490246, 199041, 4327046, 6424454, 69272964, 102827652, 27182368903,
      434917934981, 1698891161, 1696663299, 1126237699, 434917934035, 1698890882]
  | true, true, false, true =>
    stepsOf 6 [263169, 1698891010, 2162688, 4391168, 27164476300, 27182367373, 1126236931, 1126237059,
      2163787, 52495748, 1126237840, 1126237339, 1126237074, 69272650, 70387145, 70387274,
      3278208, 264065, 1126237315, 27182368391, 434917934469, 1698890896, 102827780, 69273092,
      1679885571, 6424582, 4327174, 434917933779, 1698890626]
  | true, true, true, false =>
    stepsOf 6 [197633, 1698891010, 131073, 262401, 2163200, 69271812, 2162891, 4391680,
      4391627, 21168388, 27163494279, 27163625095, 27164476812, 27182367885, 1126237443, 4327174,
      4261894, 2164486, 4393222, 1126237571, 2164299, 2164619, 52496516, 69273988,
      2164230, 3278726, 4327558, 3212934, 4261766, 4392267, 4392587, 4392198,
      1126238864, 1126238365, 1126238098, 1126237594, 4327296, 3212928, 21104260, 4327243,
      54659204, 4392710, 4327819, 4327430, 4328064, 3278598, 3278726, 4327558,
      133505, 264321, 198529, 27182302855, 434917934291, 1698891138]
  | _, _, _, _ => []

theorem chk323_2302 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = true →
    checkD (Gen.k 0 2 4 5 (by decide) (by decide) (by decide) :: (negw x 0 ++ negw y 2) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_2302 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_2302 x y p q ++
        Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw p 2 ++ negw q 3)) (S323_2302 x y p q) = true := by
  decide +kernel

theorem tag323_2302 : ∀ x y p q : Bool, ∀ g ∈ X323_2302 x y p q ++ Y323_2302 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {2,3}`, `{α,β} = {0,2}` (from `0`). -/
theorem rel323_2302 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = true) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a0 a2 c d (h1.trans h2) (h3.trans h4) h5 :: (negw x a0 ++ negw y a2) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a2 a3 c d h3 h4 h5 :: (negw p a2 ++ negw q a3))) := by
  refine ⟨(X323_2302 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_2302 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_2302 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_2302 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

/-- `X` for `{a,b} = {2,3}`, `{α,β} = {1,3}`. -/
def X323_2313 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 0 2 (by decide)]
  | false, true, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, false, true => [Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, false, true, false => [Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => []
  | true, true, true, true => [Gen.x 0 2 (by decide)]
  | _, _, _, _ => []

/-- `Y` for `{a,b} = {2,3}`, `{α,β} = {1,3}`. -/
def Y323_2313 : Bool → Bool → Bool → Bool → List (Gen 6)
  | false, false, false, false => []
  | false, false, true, true => [Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | false, true, false, true => [Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | false, true, true, false => [Gen.x 2 5 (by decide), Gen.x 3 4 (by decide), Gen.neg 2, Gen.neg 3, Gen.neg 4, Gen.neg 5]
  | true, false, false, true => [Gen.x 0 1 (by decide), Gen.x 2 5 (by decide), Gen.x 3 5 (by decide), Gen.x 4 5 (by decide), Gen.neg 2, Gen.neg 4]
  | true, false, true, false => [Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.x 4 5 (by decide)]
  | true, true, false, false => [Gen.x 0 1 (by decide), Gen.x 3 5 (by decide), Gen.neg 3, Gen.neg 5]
  | true, true, true, true => [Gen.x 0 1 (by decide)]
  | _, _, _, _ => []

/-- The chains for `{a,b} = {2,3}`, `{α,β} = {1,3}`. -/
def S323_2313 : Bool → Bool → Bool → Bool → List (GStep ((Fam ⊕ MFam) × Bool) 6)
  | false, false, false, false =>
    stepsOf 6 [1698890242, 434917933267, 1698890114]
  | false, false, true, true =>
    stepsOf 6 [262657, 197121, 4391814, 4391558, 1698890754, 3211264, 434902204805, 1126236823,
      263553, 197761, 1698890640, 434917933523, 1698890370]
  | false, true, false, true =>
    stepsOf 6 [262913, 1698890754, 4325376, 6619392, 1698825104, 1698824850, 6554496, 6554630,
      263041, 18020172679, 6554630, 1698890905, 434917933779, 1698890626]
  | false, true, true, false =>
    stepsOf 6 [197377, 1698890754, 4325376, 6619392, 1698825104, 1698824850, 6554496, 6554630,
      263041, 18020172679, 6489094, 1698890911, 434917933779, 1698890626]
  | true, false, false, true =>
    stepsOf 6 [262913, 1698890754, 4325376, 6619392, 1698825104, 1698824850, 6554496, 6423558,
      4326150, 18020173191, 1126237081, 6555142, 1126237315, 69272964, 102827652, 4392075,
      105055620, 434917934981, 1698891408, 1698890911, 5507206, 6556038, 6621318, 6556171,
      90441988, 6555851, 56887044, 106169993, 106169994, 5507462, 6556294, 265089,
      395905, 86051076, 52496388, 1696663299, 1679885827, 1663108355, 434917933779, 1698890626]
  | true, false, true, false =>
    stepsOf 6 [197377, 1698890754, 3211264, 4325632, 6619648, 434902205829, 1698825360, 1698825106,
      6554752, 103875844, 70321156, 6424070, 4326662, 36766852, 70321540, 18020173703,
      1126237847, 1126237337, 4392576, 4392582, 6489990, 198785, 69272964, 102827652,
      434917934981, 1698891161, 1696663299, 1126237699, 434917934035, 1698890882]
  | true, true, false, false =>
    stepsOf 6 [1698890754, 1126236569, 1126236803, 434917933957, 1698890384, 102827268, 69272580, 1679885059,
      434917933267, 1698890114]
  | true, true, true, true =>
    stepsOf 6 [263169, 197633, 4392326, 4392070, 1698891266, 3211264, 434902204805, 36766340,
      70321028, 1126237335, 1126236825, 4392064, 263553, 197761, 434917933957, 434917933523,
      1698890370]
  | _, _, _, _ => []

theorem chk323_2313 : ∀ x y p q : Bool, xor (xor (xor x y) p) q = false →
    checkD (Gen.k 1 3 4 5 (by decide) (by decide) (by decide) :: (negw x 1 ++ negw y 3) ++ [Gen.k 0 1 2 3 (by decide) (by decide) (by decide)])
      (X323_2313 x y p q ++ Gen.k 0 1 2 4 (by decide) (by decide) (by decide) :: Y323_2313 x y p q ++
        Gen.k 2 3 4 5 (by decide) (by decide) (by decide) :: (negw p 2 ++ negw q 3)) (S323_2313 x y p q) = true := by
  decide +kernel

theorem tag323_2313 : ∀ x y p q : Bool, ∀ g ∈ X323_2313 x y p q ++ Y323_2313 x y p q, g.tag ≠ 2 := by
  decide

/-- Subcase 3.2.3 with `{a,b} = {2,3}`, `{α,β} = {1,3}` (from `0`). -/
theorem rel323_2313 {a0 a1 a2 a3 c d : Fin n} (h1 : a0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < c) (h5 : c < d) (x y p q : Bool)
    (hpar : xor (xor (xor x y) p) q = false) :
    ∃ Xw Yw : List (Gen n), (∀ g ∈ Xw ++ Yw, g.tag ≠ 2 ∧ extent g ≤ d.val) ∧
      Derivable (Table1 n)
        (FreeMonoid.ofList (Gen.k a1 a3 c d (h2.trans h3) h4 h5 :: (negw x a1 ++ negw y a3) ++
          [Gen.k a0 a1 a2 a3 h1 h2 h3]))
        (FreeMonoid.ofList (Xw ++ Gen.k a0 a1 a2 c h1 h2 (h3.trans h4) :: Yw ++
          Gen.k a2 a3 c d h3 h4 h5 :: (negw p a2 ++ negw q a3))) := by
  refine ⟨(X323_2313 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)),
    (Y323_2313 x y p q).map (Gen.rename (emb6 h1 h2 h3 h4 h5)), ?_, ?_⟩
  · intro g hg
    rw [← List.map_append] at hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    refine ⟨by rw [tag_rename]; exact tag323_2313 x y p q g' hg', ?_⟩
    have := extent_rename_le (emb6 h1 h2 h3 h4 h5) g' 5 (extent_le_last g')
    rwa [emb6_5] at this
  · have hh := derivable_rename (emb6 h1 h2 h3 h4 h5) (checkD_sound (chk323_2313 x y p q hpar))
    rw [renW_ofList, renW_ofList] at hh
    convert hh using 2 <;>
      simp only [List.map_append, List.map_cons, List.map_nil, negw_rename, Gen.rename, emb6_0,
        emb6_1, emb6_2, emb6_3, emb6_4, emb6_5, List.cons_append, List.nil_append,
        List.append_assoc]

end QCert.LiRossSelinger
