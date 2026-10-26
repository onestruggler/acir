------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of the five-wire derivations, as trees
--
-- The derivations of Five.D take their windows as an argument (see
-- `scratchpad/five/winlib5.py`): `WsL` proves the literal windows and
-- the two-wire equations of Five.D.TR, `Ws` holds those (`lit`) and the
-- placed windows.  The statements are two Braun trees, `windowsL` and
-- `windowsP`, the n-th the statement of wlNNNN, resp. wpNNNN, for
-- n = NNNN, and `wl n W`, `wp n W` the n-th proofs; records of the
-- windows, as this module had, made a 5.2 MB interface that took 97 s
-- and 2.4 GB to check.  Five.WinInst builds them.
-- Written by `scratchpad/five/wintree5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Examples.Groups.Clifford+CS.Five.WinSig where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)
open import Data.Unit.Base using (⊤ ; tt)

open import Examples.Groups.Clifford+CS.Five.Chain using (Mac ; ⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Five.Letters
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- A Braun tree of statements: the n-th is at the root for n = 0, and
-- otherwise the ⌊(n − 1)/2⌋-th of the left subtree for n odd, of the
-- right one for n even.
data WTree : Set where
  wleaf : WTree
  wnode : WTree → List Mac → List Mac → WTree → WTree

WinT : WTree → ℕ → Set
WinT wleaf           _       = ⊤
WinT (wnode a l r b) zero    = ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
WinT (wnode a l r b) (suc n) = if n % 2 ≡ᵇ 0 then WinT a (n / 2) else WinT b (n / 2)

data WProofs : WTree → Set where
  pleaf : WProofs wleaf
  pnode : ∀ {a l r b} → WProofs a → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → WProofs b → WProofs (wnode a l r b)

private
  pick : (c : Bool) {A B : Set} → A → B → if c then A else B
  pick true  x y = x
  pick false x y = y

wget : (t : WTree) → WProofs t → (n : ℕ) → WinT t n
wget wleaf           pleaf           n       = tt
wget (wnode a l r b) (pnode pa p pb) zero    = p
wget (wnode a l r b) (pnode pa p pb) (suc n) =
  pick (n % 2 ≡ᵇ 0) (wget a pa (n / 2)) (wget b pb (n / 2))

windowsL : WTree
windowsL =
  (wnode
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乥云") (ℓ "亍乥")
                        wleaf
                      )
                      (ℓ "乽产") (ℓ "产享乽")
                      (wnode
                        wleaf
                        (ℓ "互乇互么与上与") (ℓ "与上与互乇互么")
                        wleaf
                      )
                    )
                    (ℓ "书亍") (ℓ "亍书")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京並乐") (ℓ "並京")
                        wleaf
                      )
                      (ℓ "亨乗") (ℓ "亪亨亪")
                      wleaf
                    )
                  )
                  (ℓ "乊亥") (ℓ "亦乊")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乏") (ℓ "乏亨")
                        wleaf
                      )
                      (ℓ "亨乢") (ℓ "乢亨")
                      (wnode
                        wleaf
                        (ℓ "也亳") (ℓ "亳也")
                        wleaf
                      )
                    )
                    (ℓ "二买交") (ℓ "买二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亍产亙") (ℓ "亙产")
                        wleaf
                      )
                      (ℓ "书亲亪") (ℓ "亪书亲")
                      wleaf
                    )
                  )
                )
                (ℓ "丫产") (ℓ "些丫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐个") (ℓ "个亐")
                        wleaf
                      )
                      (ℓ "丢並乩並") (ℓ "並乩並丢")
                      (wnode
                        wleaf
                        (ℓ "交") (ℓ "乄交乄")
                        wleaf
                      )
                    )
                    (ℓ "交了") (ℓ "了京交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘乳") (ℓ "乳亘")
                        wleaf
                      )
                      (ℓ "京") (ℓ "乕乳乖乳乹")
                      wleaf
                    )
                  )
                  (ℓ "丷亦") (ℓ "亦丷")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亮亮") (ℓ "了")
                        wleaf
                      )
                      (ℓ "亐么") (ℓ "么亐")
                      (wnode
                        wleaf
                        (ℓ "亯亳") (ℓ "亳亯")
                        wleaf
                      )
                    )
                    (ℓ "么亲") (ℓ "亲么")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒中上互乇互么") (ℓ "互乇互么丒中上")
                        wleaf
                      )
                      (ℓ "买亦亦") (ℓ "买")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丫亦") (ℓ "亚丫")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊乕") (ℓ "乕亊")
                        wleaf
                      )
                      (ℓ "乕亲") (ℓ "亲乕")
                      (wnode
                        wleaf
                        (ℓ "亐书") (ℓ "书二亐")
                        wleaf
                      )
                    )
                    (ℓ "乑乑") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亩亲亲") (ℓ "亩")
                        wleaf
                      )
                      (ℓ "亘丷") (ℓ "丷亘")
                      wleaf
                    )
                  )
                  (ℓ "下上") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "之亮") (ℓ "亮之")
                        wleaf
                      )
                      (ℓ "亐亘") (ℓ "亘亐")
                      (wnode
                        wleaf
                        (ℓ "丘丯之丰之丨丙") (ℓ "亏")
                        wleaf
                      )
                    )
                    (ℓ "亰乇") (ℓ "乇亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏与中与") (ℓ "与中与亏")
                        wleaf
                      )
                      (ℓ "丹于") (ℓ "亥丹")
                      wleaf
                    )
                  )
                )
                (ℓ "乴乊") (ℓ "乊乷")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亦") (ℓ "亦亘亐")
                        wleaf
                      )
                      (ℓ "亄並亄並") (ℓ "並亄並亄")
                      (wnode
                        wleaf
                        (ℓ "乇乺") (ℓ "乺乇")
                        wleaf
                      )
                    )
                    (ℓ "下亍") (ℓ "亍下么二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丙云") (ℓ "云丙")
                        wleaf
                      )
                      (ℓ "亃亲亲") (ℓ "亃")
                      wleaf
                    )
                  )
                  (ℓ "亨亲乇乎亨") (ℓ "亲乇乎")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京丒") (ℓ "丒亭京京")
                        wleaf
                      )
                      (ℓ "丒亙") (ℓ "亙丒")
                      wleaf
                    )
                    (ℓ "亐") (ℓ "丳亐丳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交些二乎些二乏与") (ℓ "些二乎些二乏与交")
                        wleaf
                      )
                      (ℓ "二交亙") (ℓ "亙二")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丶丫") (ℓ "丫乎")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买乳云") (ℓ "云乳")
                        wleaf
                      )
                      (ℓ "亨亰") (ℓ "亰亨")
                      (wnode
                        wleaf
                        (ℓ "乽乳亯") (ℓ "亯乳")
                        wleaf
                      )
                    )
                    (ℓ "亨") (ℓ "乕也乖也乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交丢亰亰亰亭乇亰亰亭么") (ℓ "丢亰亰亰亭乇亰亰亭么交")
                        wleaf
                      )
                      (ℓ "乖东亮丝") (ℓ "亮京")
                      wleaf
                    )
                  )
                  (ℓ "乥亙") (ℓ "亙乥")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐乣") (ℓ "乣亐")
                        wleaf
                      )
                      (ℓ "丢並亇並") (ℓ "並亇並丢")
                      (wnode
                        wleaf
                        (ℓ "二亘二亘二") (ℓ "二")
                        wleaf
                      )
                    )
                    (ℓ "丑丐") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "与与") []
                        wleaf
                      )
                      (ℓ "丶乎亐乎乐亐") (ℓ "丶")
                      wleaf
                    )
                  )
                )
                (ℓ "丸乊") (ℓ "乊丸")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕乕乕乕") []
                        wleaf
                      )
                      (ℓ "乹並乹並") (ℓ "並乹並乹")
                      (wnode
                        wleaf
                        (ℓ "乹亯") (ℓ "亯乹乎京")
                        wleaf
                      )
                    )
                    (ℓ "乳乒乳") (ℓ "乑")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬些些") (ℓ "丬")
                        wleaf
                      )
                      (ℓ "亰乫亲亰") (ℓ "亲")
                      wleaf
                    )
                  )
                  (ℓ "交") (ℓ "乢之乣之乎")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乬亮") (ℓ "产乬")
                        wleaf
                      )
                      (ℓ "乹並") (ℓ "並东乺")
                      wleaf
                    )
                    (ℓ "交亳") (ℓ "亳交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘临上与") (ℓ "与临")
                        wleaf
                      )
                      (ℓ "乳亭並") (ℓ "並亭")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乢乊") (ℓ "乊乎")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乤") (ℓ "乤亰")
                        wleaf
                      )
                      (ℓ "亭乇亭么並丢並") (ℓ "並丢並亭乇亭么")
                      (wnode
                        wleaf
                        (ℓ "互乇互么与中与") (ℓ "与中与互乇互么")
                        wleaf
                      )
                    )
                    (ℓ "交亃") (ℓ "亃亰交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亲亨") (ℓ "亲交")
                        wleaf
                      )
                      (ℓ "乥亮") (ℓ "亪乥")
                      wleaf
                    )
                  )
                  (ℓ "丙丘") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐乏") (ℓ "乏亐")
                        wleaf
                      )
                      (ℓ "丢並亊並") (ℓ "並亊並丢")
                      (wnode
                        wleaf
                        (ℓ "亐亘亘亘互乇亘亘互么亏") (ℓ "亘亘亘互乇亘亘互么亏亐")
                        wleaf
                      )
                    )
                    (ℓ "京亱") (ℓ "亱京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乢乥") (ℓ "乥乢")
                        wleaf
                      )
                      (ℓ "乙亦亦") (ℓ "乙")
                      wleaf
                    )
                  )
                )
                (ℓ "乥亱") (ℓ "亲乥")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亪") (ℓ "亪乒")
                        wleaf
                      )
                      (ℓ "亨乗亪亨") (ℓ "亪")
                      (wnode
                        wleaf
                        (ℓ "乹乩亰书") (ℓ "书乹")
                        wleaf
                      )
                    )
                    (ℓ "不久") (ℓ "且乆且")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏亚") (ℓ "亚亏")
                        wleaf
                      )
                      (ℓ "乩产") (ℓ "产乩")
                      wleaf
                    )
                  )
                  (ℓ "交亰亭") (ℓ "亭交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰丢") (ℓ "丢亰")
                        wleaf
                      )
                      (ℓ "亘乄交") (ℓ "乄亘")
                      wleaf
                    )
                    (ℓ "交丷") (ℓ "丷交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二些乎") (ℓ "些乎二")
                        wleaf
                      )
                      (ℓ "亐亙") (ℓ "亙亐交")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乪乊") (ℓ "乊乖")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亭亰乇亭亰么並") (ℓ "亭亰乇亭亰么並交")
                        wleaf
                      )
                      (ℓ "亐亓") (ℓ "亓亐个")
                      (wnode
                        wleaf
                        (ℓ "乏互乇互么") (ℓ "互乇互么乏")
                        wleaf
                      )
                    )
                    (ℓ "亨亨") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亨亄丢亇亨亇丢") (ℓ "亩亪")
                        wleaf
                      )
                      (ℓ "亪亮") (ℓ "亮亪")
                      wleaf
                    )
                  )
                  (ℓ "交丫") (ℓ "丫亘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨丒") (ℓ "丒亩亨亨")
                        wleaf
                      )
                      (ℓ "亐亙交") (ℓ "亙亐")
                      (wnode
                        wleaf
                        (ℓ "亰乑") (ℓ "乑亨")
                        wleaf
                      )
                    )
                    (ℓ "二") (ℓ "乇丳么丳丨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亲乎乇亨") (ℓ "亲乎乇")
                        wleaf
                      )
                      (ℓ "丯乏") (ℓ "乏丯")
                      wleaf
                    )
                  )
                )
                (ℓ "乙乥") (ℓ "乥乙")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "两乾一丠") (ℓ "丠乿")
                        wleaf
                      )
                      (ℓ "世乪") (ℓ "並乩並")
                      (wnode
                        wleaf
                        (ℓ "乎亚") (ℓ "亚乎")
                        wleaf
                      )
                    )
                    (ℓ "亐交") (ℓ "交亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亚") (ℓ "亚乳")
                        wleaf
                      )
                      (ℓ "乊亙") (ℓ "云乊")
                      wleaf
                    )
                  )
                  (ℓ "亘丨") (ℓ "丨亘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨些") (ℓ "些丨")
                        wleaf
                      )
                      (ℓ "丐乖並") (ℓ "並乕")
                      (wnode
                        wleaf
                        (ℓ "亐亏") (ℓ "亏亐")
                        wleaf
                      )
                    )
                    (ℓ "乣丢亳丣") (ℓ "亳亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐也") (ℓ "也亘亐")
                        wleaf
                      )
                      (ℓ "乇乎交乎乐交") (ℓ "乇")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丳丫") (ℓ "丫之")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亇") (ℓ "亇亄")
                        wleaf
                      )
                      (ℓ "乩並丢並") (ℓ "並丢並乩")
                      (wnode
                        wleaf
                        (ℓ "丞主上互乇互么") (ℓ "互乇互么丞主上")
                        wleaf
                      )
                    )
                    (ℓ "亰") (ℓ "亃亰亃")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交") (ℓ "亰亳乗亳亰乗")
                        wleaf
                      )
                      (ℓ "乺亦") (ℓ "亦乺")
                      wleaf
                    )
                  )
                  (ℓ "二乒") (ℓ "乒二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏亓") (ℓ "亓乏丩亐")
                        wleaf
                      )
                      (ℓ "京之") (ℓ "之京")
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "些乎些乏些乎些乏")
                        wleaf
                      )
                    )
                    (ℓ "乙亃乙") (ℓ "乘")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亦一下") (ℓ "一下亦")
                        wleaf
                      )
                      (ℓ "二") (ℓ "交产丸产交丸")
                      wleaf
                    )
                  )
                )
                (ℓ "二丫") (ℓ "丫二")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨並义") (ℓ "並亨")
                        wleaf
                      )
                      (ℓ "交亪京") (ℓ "亪交")
                      (wnode
                        wleaf
                        (ℓ "亰乫") (ℓ "书亰书")
                        wleaf
                      )
                    )
                    (ℓ "义亍") (ℓ "亍义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亨") (ℓ "产亰产")
                        wleaf
                      )
                      (ℓ "亨产") (ℓ "产亨")
                      wleaf
                    )
                  )
                  (ℓ "亐") (ℓ "亘亚义亚亘义")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "乗京乗")
                        wleaf
                      )
                      (ℓ "丘云") (ℓ "云丘")
                      wleaf
                    )
                    (ℓ "丞交丟") (ℓ "产")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇与") (ℓ "与乇")
                        wleaf
                      )
                      (ℓ "交亨亲乎亨亲乏並") (ℓ "亨亲乎亨亲乏並交")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丰丫") (ℓ "丫么")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄丢") (ℓ "丢亄")
                        wleaf
                      )
                      (ℓ "亰产") (ℓ "产亰亨")
                      (wnode
                        wleaf
                        (ℓ "上与主与") (ℓ "与主与上")
                        wleaf
                      )
                    )
                    (ℓ "亨乳") (ℓ "乳亰亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亦乫亦交乫") (ℓ "京")
                        wleaf
                      )
                      (ℓ "亘些") (ℓ "些丱亘")
                      wleaf
                    )
                  )
                  (ℓ "乐丫") (ℓ "丫丸")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乶亐亐") (ℓ "乶")
                        wleaf
                      )
                      (ℓ "丙交") (ℓ "亦丙")
                      (wnode
                        wleaf
                        (ℓ "乣亳") (ℓ "亳乣")
                        wleaf
                      )
                    )
                    (ℓ "交京交京交") (ℓ "交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "与上与") (ℓ "一下")
                        wleaf
                      )
                      (ℓ "为亦") (ℓ "亦为亏")
                      wleaf
                    )
                  )
                )
                (ℓ "亄乊") (ℓ "乊亇")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹亊乹亊乹亊") (ℓ "丢丢丢")
                        wleaf
                      )
                      (ℓ "丌亘") (ℓ "亙丌")
                      (wnode
                        wleaf
                        (ℓ "乒亓互乇互么") (ℓ "互乇互么乒亓")
                        wleaf
                      )
                    )
                    (ℓ "亘") (ℓ "丯乶丰乶丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄些") (ℓ "些乄产")
                        wleaf
                      )
                      (ℓ "乘亲") (ℓ "产乘")
                      wleaf
                    )
                  )
                  (ℓ "交亨亲") (ℓ "亲交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘丱些亘") (ℓ "些")
                        wleaf
                      )
                      (ℓ "丢亦") (ℓ "亦丢")
                      wleaf
                    )
                    (ℓ "亨乹") (ℓ "乹亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乤亳亰") (ℓ "亳")
                        wleaf
                      )
                      (ℓ "丶乇") (ℓ "乇丶")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乥乼") (ℓ "乬乥")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亍丸亍二丸丸二亍丸亍二") []
                        wleaf
                      )
                      (ℓ "亄並乕並") (ℓ "並乕並亄")
                      (wnode
                        wleaf
                        (ℓ "亐二亐二亐") (ℓ "亐")
                        wleaf
                      )
                    )
                    (ℓ "二乎") (ℓ "乎二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交") (ℓ "京交京")
                        wleaf
                      )
                      (ℓ "乢亙") (ℓ "亙乢")
                      wleaf
                    )
                  )
                  (ℓ "丱亦") (ℓ "亦丱亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亙") (ℓ "亙买")
                        wleaf
                      )
                      (ℓ "亃亰亰") (ℓ "亃")
                      (wnode
                        wleaf
                        (ℓ "二亓交") (ℓ "交二二亓")
                        wleaf
                      )
                    )
                    (ℓ "乪丝") (ℓ "丝乪")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄丢亄") []
                        wleaf
                      )
                      (ℓ "二") (ℓ "个二个")
                      wleaf
                    )
                  )
                )
                (ℓ "乊丂") (ℓ "丂乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亃亲乎亲乏") (ℓ "亲乎亨亲乏交亄乕乕亄交丢乩")
                        wleaf
                      )
                      (ℓ "丷丗") (ℓ "丗丷")
                      (wnode
                        wleaf
                        (ℓ "乶亓") (ℓ "亓乶亏")
                        wleaf
                      )
                    )
                    (ℓ "九") (ℓ "丰不丰丌丰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乺") (ℓ "乺亨")
                        wleaf
                      )
                      (ℓ "乏么交么义交") (ℓ "乏")
                      wleaf
                    )
                  )
                  (ℓ "乇云") (ℓ "云乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "亰亱义亱亰义")
                        wleaf
                      )
                      (ℓ "京交亪") (ℓ "亪交")
                      wleaf
                    )
                    (ℓ "二产") (ℓ "产二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎些乎些乏") (ℓ "些乎些乏乎")
                        wleaf
                      )
                      (ℓ "乇亲乎亲乏") (ℓ "亲乎亲乏乇")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "乥乥") []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亮亭乇亭么") (ℓ "亭乇亭么乒亮")
                        wleaf
                      )
                      (ℓ "产亳") (ℓ "亳产享")
                      (wnode
                        wleaf
                        (ℓ "交互亘乇互亘么与") (ℓ "互亘乇互亘么与交")
                        wleaf
                      )
                    )
                    (ℓ "亨乶") (ℓ "乶京亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亍") (ℓ "亍亘交")
                        wleaf
                      )
                      (ℓ "书亪") (ℓ "亪亮书")
                      wleaf
                    )
                  )
                  (ℓ "丌乇丬么丬丯丌一") (ℓ "丌乇丳么丳丨丌一")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亙个亙亘个") (ℓ "交")
                        wleaf
                      )
                      (ℓ "亲乎亲乏並亄並") (ℓ "並亄並亲乎亲乏")
                      (wnode
                        wleaf
                        (ℓ "二乳") (ℓ "乳亘二")
                        wleaf
                      )
                    )
                    (ℓ "上丷") (ℓ "丠丶丠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "並丢並丢") (ℓ "一")
                        wleaf
                      )
                      (ℓ "丯乎") (ℓ "乎丯")
                      wleaf
                    )
                  )
                )
                (ℓ "丘乥") (ℓ "乥丞")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨丠") (ℓ "丠亨")
                        wleaf
                      )
                      (ℓ "亄並乩並") (ℓ "並乩並亄")
                      (wnode
                        wleaf
                        (ℓ "亨亯") (ℓ "亯亨交")
                        wleaf
                      )
                    )
                    (ℓ "亐") (ℓ "丨乳丩乳丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓二二") (ℓ "亓")
                        wleaf
                      )
                      (ℓ "也之也") (ℓ "乊")
                      wleaf
                    )
                  )
                  (ℓ "乕亦") (ℓ "亦乕")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乬亭") (ℓ "亥乬")
                        wleaf
                      )
                      (ℓ "京") (ℓ "乎争乏争乕")
                      (wnode
                        wleaf
                        (ℓ "也亯") (ℓ "亯也亳")
                        wleaf
                      )
                    )
                    (ℓ "亰乖") (ℓ "乖亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "互乇互么与临与") (ℓ "与临与互乇互么")
                        wleaf
                      )
                      (ℓ "丹亥") (ℓ "于丹")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乻乥") (ℓ "乥乫")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊乩") (ℓ "乩亊")
                        wleaf
                      )
                      (ℓ "乽争乽") (ℓ "乼")
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "义亨义")
                        wleaf
                      )
                    )
                    (ℓ "亐乐云亐") (ℓ "云")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊亰亊丢") (ℓ "亲")
                        wleaf
                      )
                      (ℓ "京亮乗") (ℓ "亮京")
                      wleaf
                    )
                  )
                  (ℓ "二亍义") (ℓ "亍二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐个为") (ℓ "为亐")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "乢了乣了乹")
                      (wnode
                        wleaf
                        (ℓ "乎乩") (ℓ "乩乎")
                        wleaf
                      )
                    )
                    (ℓ "乺世亱丗") (ℓ "亱亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "中与") (ℓ "与丒中上")
                        wleaf
                      )
                      (ℓ "二个亏二") (ℓ "亏")
                      wleaf
                    )
                  )
                )
                (ℓ "亄乥") (ℓ "乥亄")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乼亦") (ℓ "亪乼")
                        wleaf
                      )
                      (ℓ "交丰") (ℓ "丰交")
                      (wnode
                        wleaf
                        (ℓ "交亏") (ℓ "亏亐交")
                        wleaf
                      )
                    )
                    (ℓ "丨乇二乇义二") (ℓ "丨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亭义亭京义") (ℓ "亰")
                        wleaf
                      )
                      (ℓ "亐个") (ℓ "亓亐亓")
                      wleaf
                    )
                  )
                  (ℓ "乏上云下") (ℓ "云亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二些") (ℓ "些二")
                        wleaf
                      )
                      (ℓ "丐乖亭乇亭么") (ℓ "亭乇亭么丐乖")
                      wleaf
                    )
                    (ℓ "亐乜") (ℓ "乜交亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亳") (ℓ "亳乳")
                        wleaf
                      )
                      (ℓ "之亪亲乎亲乏") (ℓ "亲乎亲乏之亪")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "乒乊") (ℓ "乊书")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "么亭乇亭么") (ℓ "亭乇亭么么")
                        wleaf
                      )
                      (ℓ "串亥") (ℓ "互串")
                      (wnode
                        wleaf
                        (ℓ "么互乇互么") (ℓ "互乇互么么")
                        wleaf
                      )
                    )
                    (ℓ "亍亙") (ℓ "亙亍")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹亊亭乇亭么交亊交亭乇亭么") (ℓ "亭乇亭么交亊亭乇亭么交亊乹")
                        wleaf
                      )
                      (ℓ "些些") []
                      wleaf
                    )
                  )
                  (ℓ "么丫") (ℓ "丫丰")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乢亍") (ℓ "亍乢")
                        wleaf
                      )
                      (ℓ "亄並亇並") (ℓ "並亇並亄")
                      (wnode
                        wleaf
                        (ℓ "亰亳") (ℓ "亳乤亰")
                        wleaf
                      )
                    )
                    (ℓ "于于") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "九丫") (ℓ "丫习")
                        wleaf
                      )
                      (ℓ "交亦") (ℓ "亦交乐")
                      wleaf
                    )
                  )
                )
                (ℓ "乊亭") (ℓ "亱乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亇") (ℓ "丢丢丢")
                        wleaf
                      )
                      (ℓ "亦並乹並") (ℓ "並乹並亦")
                      (wnode
                        wleaf
                        (ℓ "乺乏京乏乐京") (ℓ "乺")
                        wleaf
                      )
                    )
                    (ℓ "二义") (ℓ "亍二亍")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘丨乜丩乜乇丙") (ℓ "亏")
                        wleaf
                      )
                      (ℓ "也亲") (ℓ "亲也")
                      wleaf
                    )
                  )
                  (ℓ "亲並") (ℓ "並书亲")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘丱些") (ℓ "些亘")
                        wleaf
                      )
                      (ℓ "亄並") (ℓ "並丒亄丢")
                      wleaf
                    )
                    (ℓ "两亨严") (ℓ "享")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乤亳") (ℓ "亳亰")
                        wleaf
                      )
                      (ℓ "亭亱亱") (ℓ "亭")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乭乊") (ℓ "乊乙")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交") (ℓ "丸交丸")
                        wleaf
                      )
                      (ℓ "丢並乕並") (ℓ "並乕並丢")
                      (wnode
                        wleaf
                        (ℓ "书亯") (ℓ "亯书享")
                        wleaf
                      )
                    )
                    (ℓ "亘") (ℓ "丶书丷书丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丙亓") (ℓ "亓丙")
                        wleaf
                      )
                      (ℓ "亘亙") (ℓ "亙乤亘")
                      wleaf
                    )
                  )
                  (ℓ "丗世") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亲乫") (ℓ "亲亰")
                        wleaf
                      )
                      (ℓ "亄並亊並") (ℓ "並亊並亄")
                      (wnode
                        wleaf
                        (ℓ "丘") (ℓ "与临与临")
                        wleaf
                      )
                    )
                    (ℓ "丞亰丟") (ℓ "亲")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丫且") (ℓ "与丫")
                        wleaf
                      )
                      (ℓ "乽亦") (ℓ "亦乽")
                      wleaf
                    )
                  )
                )
                (ℓ "乄丫") (ℓ "丫丬")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亄交交") (ℓ "交亄")
                        wleaf
                      )
                      (ℓ "亘丸") (ℓ "亚亘亚")
                      (wnode
                        wleaf
                        (ℓ "亰乺") (ℓ "乺亰")
                        wleaf
                      )
                    )
                    (ℓ "丰么二么义二") (ℓ "丰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘二产") (ℓ "产亘")
                        wleaf
                      )
                      (ℓ "乇产") (ℓ "产乇")
                      wleaf
                    )
                  )
                  (ℓ "交乢交亰亭乇") (ℓ "亭乇乢亰")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亨亇丢亄亨亄丢") (ℓ "亪亩")
                        wleaf
                      )
                      (ℓ "乄丬乄") (ℓ "丫")
                      wleaf
                    )
                    (ℓ "乕产") (ℓ "产乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭亳") (ℓ "亳乭")
                        wleaf
                      )
                      (ℓ "亨乎亲") (ℓ "乎亲亨")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乩乥") (ℓ "乥乹")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏亭乇亭么") (ℓ "亭乇亭么乏")
                        wleaf
                      )
                      (ℓ "亰产亨") (ℓ "产亰")
                      (wnode
                        wleaf
                        (ℓ "乇亯") (ℓ "亯乇")
                        wleaf
                      )
                    )
                    (ℓ "乥互") (ℓ "于乥")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "京")
                        wleaf
                      )
                      (ℓ "产亮") (ℓ "亮产")
                      wleaf
                    )
                  )
                  (ℓ "交乥") (ℓ "乥交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒亚") (ℓ "亚丒")
                        wleaf
                      )
                      (ℓ "亨争") (ℓ "争亨")
                      (wnode
                        wleaf
                        (ℓ "么些") (ℓ "些么")
                        wleaf
                      )
                    )
                    (ℓ "丒京专") (ℓ "亭")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞") (ℓ "並亊並亊")
                        wleaf
                      )
                      (ℓ "乏云") (ℓ "云乏")
                      wleaf
                    )
                  )
                )
                (ℓ "乊乥") (ℓ "乑乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亓") (ℓ "亓也些")
                        wleaf
                      )
                      (ℓ "世乪亭乇亭么") (ℓ "亭乇亭么世乪")
                      (wnode
                        wleaf
                        (ℓ "乒享") (ℓ "享乒")
                        wleaf
                      )
                    )
                    (ℓ "二乣") (ℓ "乣二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亨") (ℓ "亲交亲")
                        wleaf
                      )
                      (ℓ "亰乫") (ℓ "亲亰亲")
                      wleaf
                    )
                  )
                  (ℓ "亙亙") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "亰亨亰")
                        wleaf
                      )
                      (ℓ "世乪亮") (ℓ "亮世乪")
                      (wnode
                        wleaf
                        (ℓ "丞主上亚") (ℓ "亚丞主上")
                        wleaf
                      )
                    )
                    (ℓ "亨亳") (ℓ "亳交亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乐") (ℓ "亯京亯")
                        wleaf
                      )
                      (ℓ "乐交亦") (ℓ "亦交")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丷乊") (ℓ "乊丷")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亊") (ℓ "亊亇")
                        wleaf
                      )
                      (ℓ "亊並丢並") (ℓ "並丢並亊")
                      (wnode
                        wleaf
                        (ℓ "主与上与") (ℓ "与上与主")
                        wleaf
                      )
                    )
                    (ℓ "交") (ℓ "乙交乙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亱京") (ℓ "亱交")
                        wleaf
                      )
                      (ℓ "丶乶") (ℓ "乶丶")
                      wleaf
                    )
                  )
                  (ℓ "交丯") (ℓ "丯交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎丨亐为") (ℓ "为乎")
                        wleaf
                      )
                      (ℓ "亐乐") (ℓ "云亐云")
                      (wnode
                        wleaf
                        (ℓ "临亘临上") (ℓ "亚")
                        wleaf
                      )
                    )
                    (ℓ "丌乎丬乏丬丶不") (ℓ "云")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丐丩与") (ℓ "与丨")
                        wleaf
                      )
                      (ℓ "乙亱") (ℓ "亱乙亦")
                      wleaf
                    )
                  )
                )
                (ℓ "丬丫") (ℓ "丫乄")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亚") (ℓ "亚亐")
                        wleaf
                      )
                      (ℓ "丬乄丬") (ℓ "丫")
                      (wnode
                        wleaf
                        (ℓ "乺亲") (ℓ "亲乺乪亰")
                        wleaf
                      )
                    )
                    (ℓ "乆") (ℓ "丨不丨丌丨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘丨也丩也丯丙") (ℓ "亏")
                        wleaf
                      )
                      (ℓ "也亙亙") (ℓ "也")
                      wleaf
                    )
                  )
                  (ℓ "亭並") (ℓ "並乳亭")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乙交交") (ℓ "乙")
                        wleaf
                      )
                      (ℓ "亦亮") (ℓ "亪亮亦")
                      wleaf
                    )
                    (ℓ "交乺") (ℓ "乺交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒中上些乎些乏") (ℓ "些乎些乏丒中上")
                        wleaf
                      )
                      (ℓ "乜亙") (ℓ "亙乜")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丒乢之乣之乎丒一") (ℓ "丒乢之乣之乎丒丂")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢亭乇亭么") (ℓ "亭乇亭么丢")
                        wleaf
                      )
                      (ℓ "串产") (ℓ "亓串")
                      (wnode
                        wleaf
                        (ℓ "书亨亨") (ℓ "书")
                        wleaf
                      )
                    )
                    (ℓ "亘乑") (ℓ "乑二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "之些") (ℓ "些之亓")
                        wleaf
                      )
                      (ℓ "丶丯亘书") (ℓ "书丶")
                      wleaf
                    )
                  )
                  (ℓ "二") (ℓ "丯之丰之丨")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "之亲") (ℓ "亲之亮")
                        wleaf
                      )
                      (ℓ "亘丩") (ℓ "丩亘")
                      (wnode
                        wleaf
                        (ℓ "亨亳") (ℓ "亳亨交")
                        wleaf
                      )
                    )
                    (ℓ "二书") (ℓ "书二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏亓亦") (ℓ "亦亓")
                        wleaf
                      )
                      (ℓ "买为买") (ℓ "丹")
                      wleaf
                    )
                  )
                )
                (ℓ "亊乥") (ℓ "乥亇")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕亲乎亲乏") (ℓ "亲乎亲乏乕")
                        wleaf
                      )
                      (ℓ "丢並亄並") (ℓ "並亄並丢")
                      (wnode
                        wleaf
                        (ℓ "二乒二亓") (ℓ "乒亓")
                        wleaf
                      )
                    )
                    (ℓ "上亍") (ℓ "亍上乇二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乪亮") (ℓ "亮乪")
                        wleaf
                      )
                      (ℓ "亐产") (ℓ "产亐二")
                      wleaf
                    )
                  )
                  (ℓ "乏亙") (ℓ "亙乏")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "並二並")
                        wleaf
                      )
                      (ℓ "亊並") (ℓ "並丞亊丢")
                      wleaf
                    )
                    (ℓ "亰享") (ℓ "享亰交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亯") (ℓ "亯交")
                        wleaf
                      )
                      (ℓ "乒亙") (ℓ "亙乒亍")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "争乥") (ℓ "乥了")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "並並") []
                        wleaf
                      )
                      (ℓ "丐乖") (ℓ "並乕並")
                      (wnode
                        wleaf
                        (ℓ "乥亩") (ℓ "亭乥")
                        wleaf
                      )
                    )
                    (ℓ "交") (ℓ "乭交乭")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亚亚") (ℓ "丬")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "乤亘乤")
                      wleaf
                    )
                  )
                  (ℓ "亮並") (ℓ "並乒亮")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨丹") (ℓ "丹乎")
                        wleaf
                      )
                      (ℓ "亘亍交") (ℓ "亍亘")
                      (wnode
                        wleaf
                        (ℓ "临") (ℓ "丰丙丰丘丰")
                        wleaf
                      )
                    )
                    (ℓ "亓亓") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交") (ℓ "买交买")
                        wleaf
                      )
                      (ℓ "为亏") (ℓ "亏为")
                      wleaf
                    )
                  )
                )
                (ℓ "乊亩") (ℓ "亪乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇乩乩亇丢") (ℓ "了")
                        wleaf
                      )
                      (ℓ "亚亚") []
                      (wnode
                        wleaf
                        (ℓ "京亯乫亯京乫乥") (ℓ "乥亨享乻享亨乻")
                        wleaf
                      )
                    )
                    (ℓ "丌乞") (ℓ "业九业")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交产义") (ℓ "产交")
                        wleaf
                      )
                      (ℓ "交京亪京") (ℓ "亪京交")
                      wleaf
                    )
                  )
                  (ℓ "乒亍") (ℓ "亍乒")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乤亓") (ℓ "亓乤二")
                        wleaf
                      )
                      (ℓ "交丨") (ℓ "丨交")
                      wleaf
                    )
                    (ℓ "亰享交") (ℓ "享亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "临与临与") (ℓ "与临与临")
                        wleaf
                      )
                      (ℓ "书亍亍") (ℓ "书")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (ℓ "丶乊") (ℓ "乊丶")
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亭亦") (ℓ "亦亭亱")
                        wleaf
                      )
                      (ℓ "产享") (ℓ "享产")
                      (wnode
                        wleaf
                        (ℓ "丘临上互乇互么") (ℓ "互乇互么丘临上")
                        wleaf
                      )
                    )
                    (ℓ "亨") (ℓ "书亨书")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乐") (ℓ "乐京")
                        wleaf
                      )
                      (ℓ "交亮亨") (ℓ "亮交")
                      wleaf
                    )
                  )
                  (ℓ "乹乼") (ℓ "乼乹")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乽交交") (ℓ "乽")
                        wleaf
                      )
                      (ℓ "亘丸亚亘") (ℓ "亚")
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "乒二乒")
                        wleaf
                      )
                    )
                    (ℓ "乱") (ℓ "丷不丷丌丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘") (ℓ "並亇並亇")
                        wleaf
                      )
                      (ℓ "丰乎") (ℓ "乎丰")
                      wleaf
                    )
                  )
                )
                (ℓ "两乼") (ℓ "乼丞")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "丠亨丠")
                        wleaf
                      )
                      (ℓ "乩並乩並") (ℓ "並乩並乩")
                      (wnode
                        wleaf
                        (ℓ "交丬") (ℓ "丬亘交")
                        wleaf
                      )
                    )
                    (ℓ "京京") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亓二") (ℓ "亓亘")
                        wleaf
                      )
                      (ℓ "云亙") (ℓ "亙云")
                      wleaf
                    )
                  )
                  (ℓ "丨亦") (ℓ "亦丨")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乬产") (ℓ "亮乬")
                        wleaf
                      )
                      (ℓ "书二二") (ℓ "书")
                      (wnode
                        wleaf
                        (ℓ "亘亐亘亐亘") (ℓ "亘")
                        wleaf
                      )
                    )
                    (ℓ "亍交交") (ℓ "亍")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏丢亯丣") (ℓ "亯京")
                        wleaf
                      )
                      (ℓ "为买为") (ℓ "丹")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乐乊") (ℓ "乊乤")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩乹") (ℓ "乹乩")
                        wleaf
                      )
                      (ℓ "争享") (ℓ "享争产")
                      (wnode
                        wleaf
                        (ℓ "亨义享") (ℓ "享亨")
                        wleaf
                      )
                    )
                    (ℓ "亐") (ℓ "丶乒丷乒丨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒乩乙乪乙乇专") (ℓ "亩")
                        wleaf
                      )
                      (ℓ "丯些") (ℓ "些丯")
                      wleaf
                    )
                  )
                  (ℓ "二义亍二") (ℓ "亍")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亮") (ℓ "亮了")
                        wleaf
                      )
                      (ℓ "京") (ℓ "之京之")
                      (wnode
                        wleaf
                        (ℓ "乩与") (ℓ "与乩")
                        wleaf
                      )
                    )
                    (ℓ "丘亰丙") (ℓ "亱")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒中上与") (ℓ "与中")
                        wleaf
                      )
                      (ℓ "二") (ℓ "丯乄丰乄乇")
                      wleaf
                    )
                  )
                )
                (ℓ "丹乊") (ℓ "乊丹")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "争亪亪") (ℓ "争")
                        wleaf
                      )
                      (ℓ "亊並亄並") (ℓ "並亄並亊")
                      (wnode
                        wleaf
                        (ℓ "丘丵") (ℓ "与临与")
                        wleaf
                      )
                    )
                    (ℓ "下么二么义二") (ℓ "下")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亰亰亰亭乇亰亰亭么亪") (ℓ "亰亰亰亭乇亰亰亭么亪京")
                        wleaf
                      )
                      (ℓ "乘亱") (ℓ "亦乘")
                      wleaf
                    )
                  )
                  (ℓ "亐丯") (ℓ "丯亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京丢") (ℓ "丢京")
                        wleaf
                      )
                      (ℓ "亐丘") (ℓ "丘亐")
                      wleaf
                    )
                    (ℓ "交丳") (ℓ "丳亐交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳互与") (ℓ "与互")
                        wleaf
                      )
                      (ℓ "二並") (ℓ "並二")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "乕乥") (ℓ "乥乕")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乳亰亭") (ℓ "乳亭")
                        wleaf
                      )
                      (ℓ "串亓") (ℓ "产串")
                      (wnode
                        wleaf
                        (ℓ "亘乳亘互") (ℓ "乳互")
                        wleaf
                      )
                    )
                    (ℓ "乳亍") (ℓ "亍乳亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亰亰亭乇亰亰亭么") (ℓ "亰亰亭乇亰亰亭么交")
                        wleaf
                      )
                      (ℓ "乖东") (ℓ "东乖")
                      wleaf
                    )
                  )
                  (ℓ "义丫") (ℓ "丫丱")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亲乎亲乏") (ℓ "亲乎亨亲乏交亇乩乩亇交丢乕")
                        wleaf
                      )
                      (ℓ "乩並亇並") (ℓ "並亇並乩")
                      (wnode
                        wleaf
                        (ℓ "乑亱") (ℓ "亪乑")
                        wleaf
                      )
                    )
                    (ℓ "丰丑") (ℓ "丑丰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "中丫") (ℓ "丫久")
                        wleaf
                      )
                      (ℓ "交乐") (ℓ "亦交亦")
                      wleaf
                    )
                  )
                )
                (ℓ "乱丫") (ℓ "丫乴")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹乹乹乹") []
                        wleaf
                      )
                      (ℓ "亇並乹並") (ℓ "並乹並亇")
                      (wnode
                        wleaf
                        (ℓ "乹乎京乎乐京") (ℓ "乹")
                        wleaf
                      )
                    )
                    (ℓ "亰亨亰亨亰") (ℓ "亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亰亮") (ℓ "亮亰")
                        wleaf
                      )
                      (ℓ "乙亲") (ℓ "亲乙产")
                      wleaf
                    )
                  )
                  (ℓ "交亙") (ℓ "亙交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬些") (ℓ "些丬")
                        wleaf
                      )
                      (ℓ "丒亄丢亪") (ℓ "亪丒亄丢")
                      wleaf
                    )
                    (ℓ "亨享") (ℓ "享亨义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京丘") (ℓ "丘京")
                        wleaf
                      )
                      (ℓ "亭亱亦") (ℓ "亦亭")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丸丫") (ℓ "丫乐")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐") (ℓ "乤亐乤")
                        wleaf
                      )
                      (ℓ "亘上") (ℓ "上亘")
                      (wnode
                        wleaf
                        (ℓ "些乎些乏与中与") (ℓ "与中与些乎些乏")
                        wleaf
                      )
                    )
                    (ℓ "亰亰") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丶亏") (ℓ "亏丶")
                        wleaf
                      )
                      (ℓ "丰乥") (ℓ "乥丷")
                      wleaf
                    )
                  )
                  (ℓ "乏丗") (ℓ "丗乏")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亓") (ℓ "亓丨")
                        wleaf
                      )
                      (ℓ "乩並亊並") (ℓ "並亊並乩")
                      (wnode
                        wleaf
                        (ℓ "中上中") []
                        wleaf
                      )
                    )
                    (ℓ "亰乎") (ℓ "乎亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乥丠") (ℓ "业乥")
                        wleaf
                      )
                      (ℓ "二亦") (ℓ "亦二亐")
                      wleaf
                    )
                  )
                )
                (ℓ "乇乊") (ℓ "乊乇")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乼亪") (ℓ "亦乼")
                        wleaf
                      )
                      (ℓ "丘亘丙") (ℓ "亚")
                      (wnode
                        wleaf
                        (ℓ "亰乩") (ℓ "乩亰")
                        wleaf
                      )
                    )
                    (ℓ "丯乇二乇义二") (ℓ "丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘乒二") (ℓ "乒亘")
                        wleaf
                      )
                      (ℓ "乎产") (ℓ "产乎乇交")
                      wleaf
                    )
                  )
                  (ℓ "丒乹乒乺乒乕专") (ℓ "亭")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亓") (ℓ "亓二")
                        wleaf
                      )
                      (ℓ "乄交交") (ℓ "乄")
                      wleaf
                    )
                    (ℓ "亨亰产") (ℓ "产亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "书些些乎些乏") (ℓ "些乎些乏书些")
                        wleaf
                      )
                      (ℓ "交亨交亨交") (ℓ "交")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乺乥") (ℓ "乥乪")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "书亲亭乇亭么") (ℓ "亭乇亭么书亲")
                        wleaf
                      )
                      (ℓ "丳亓") (ℓ "亓丳")
                      (wnode
                        wleaf
                        (ℓ "丒丶乒丷乒丨专") (ℓ "互")
                        wleaf
                      )
                    )
                    (ℓ "乥亍") (ℓ "云乥")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "亇亨亇丢亰亇亨亇丢亰")
                        wleaf
                      )
                      (ℓ "亪产") (ℓ "产亪亮")
                      wleaf
                    )
                  )
                  (ℓ "交乊") (ℓ "乊交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨丢") (ℓ "丢亨")
                        wleaf
                      )
                      (ℓ "争乽争") (ℓ "乼")
                      (wnode
                        wleaf
                        (ℓ "京享交") (ℓ "享京")
                        wleaf
                      )
                    )
                    (ℓ "京乇") (ℓ "乇京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒") (ℓ "並亄並亄")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "乎为乏为丨")
                      wleaf
                    )
                  )
                )
                (ℓ "丒乊") (ℓ "乊丘")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰之京") (ℓ "之亰")
                        wleaf
                      )
                      (ℓ "亲乎亲乏並乩並") (ℓ "並乩並亲乎亲乏")
                      (wnode
                        wleaf
                        (ℓ "书享") (ℓ "享书")
                        wleaf
                      )
                    )
                    (ℓ "二乳亘") (ℓ "乳二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐") (ℓ "丨买丩买乎")
                        wleaf
                      )
                      (ℓ "乊亓") (ℓ "些乊")
                      wleaf
                    )
                  )
                  (ℓ "乣上亙下") (ℓ "亙亘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亪亮产") (ℓ "产亪")
                        wleaf
                      )
                      (ℓ "乕並") (ℓ "並丐乖")
                      (wnode
                        wleaf
                        (ℓ "乎亏") (ℓ "亏乎")
                        wleaf
                      )
                    )
                    (ℓ "亳亳") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亘亐亘亐") (ℓ "亐")
                        wleaf
                      )
                      (ℓ "乏亦") (ℓ "亦乏")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丘乢之乣之乎丘一") (ℓ "丘乢之乣之乎丘丂")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交") (ℓ "个交个")
                        wleaf
                      )
                      (ℓ "亄並丢並") (ℓ "並丢並亄")
                      (wnode
                        wleaf
                        (ℓ "主与") (ℓ "与丞主上")
                        wleaf
                      )
                    )
                    (ℓ "交") (ℓ "乇乳么乳乢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交丩") (ℓ "丩交")
                        wleaf
                      )
                      (ℓ "乶亦") (ℓ "亦乶")
                      wleaf
                    )
                  )
                  (ℓ "业个个") (ℓ "业")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亓") (ℓ "亓丩")
                        wleaf
                      )
                      (ℓ "京亰京亰京") (ℓ "京")
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "互乇互么互乇互么")
                        wleaf
                      )
                    )
                    (ℓ "交亰交亰交") (ℓ "交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "上与中与") (ℓ "与中与上")
                        wleaf
                      )
                      (ℓ "亰乻亱亰") (ℓ "亱")
                      wleaf
                    )
                  )
                )
                (ℓ "乏丫") (ℓ "丫丷")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨义") (ℓ "义亨")
                        wleaf
                      )
                      (ℓ "京") (ℓ "乎亃乏亃乹")
                      (wnode
                        wleaf
                        (ℓ "亏产") (ℓ "产亏亓")
                        wleaf
                      )
                    )
                    (ℓ "乄亍") (ℓ "亍乄")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亰亨") (ℓ "亰")
                        wleaf
                      )
                      (ℓ "也云") (ℓ "云也亙")
                      wleaf
                    )
                  )
                  (ℓ "交") (ℓ "乎书乏书乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乙交") (ℓ "乙亰")
                        wleaf
                      )
                      (ℓ "乒亮並") (ℓ "並亮")
                      wleaf
                    )
                    (ℓ "产产") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "么与") (ℓ "与么")
                        wleaf
                      )
                      (ℓ "书亲亲乎亲乏") (ℓ "亲乎亲乏书亲")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丫一") (ℓ "一丫")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊丢") (ℓ "丢亊")
                        wleaf
                      )
                      (ℓ "乄产") (ℓ "产乄")
                      (wnode
                        wleaf
                        (ℓ "些乎些乏与主与") (ℓ "与主与些乎些乏")
                        wleaf
                      )
                    )
                    (ℓ "亰乒") (ℓ "乒亨亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京也亰") (ℓ "也京")
                        wleaf
                      )
                      (ℓ "丷丰亘丰丱亘") (ℓ "丷")
                      wleaf
                    )
                  )
                  (ℓ "临丫") (ℓ "丫乌")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊乹乹亊丢") (ℓ "争")
                        wleaf
                      )
                      (ℓ "丘予") (ℓ "並亇並")
                      (wnode
                        wleaf
                        (ℓ "乻产") (ℓ "产乻亨")
                        wleaf
                      )
                    )
                    (ℓ "丌乢丳乣丳丶不") (ℓ "亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "与乫乫") (ℓ "与")
                        wleaf
                      )
                      (ℓ "亏亦") (ℓ "亦亏")
                      wleaf
                    )
                  )
                )
                (ℓ "了乊") (ℓ "乊亃")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "亲乎亲乏亲乎亲乏")
                        wleaf
                      )
                      (ℓ "丌亐") (ℓ "云丌")
                      (wnode
                        wleaf
                        (ℓ "丞丶乒丷乒丨丟") (ℓ "亓")
                        wleaf
                      )
                    )
                    (ℓ "二丌") (ℓ "丌亍")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄产产") (ℓ "乄")
                        wleaf
                      )
                      (ℓ "乘亦") (ℓ "亱乘")
                      wleaf
                    )
                  )
                  (ℓ "丞乹书乺书乩丟") (ℓ "亲")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交些") (ℓ "些交二")
                        wleaf
                      )
                      (ℓ "丞亊丢並") (ℓ "並亊")
                      wleaf
                    )
                    (ℓ "交产") (ℓ "产交义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交二交二交") (ℓ "交")
                        wleaf
                      )
                      (ℓ "么亮") (ℓ "亮么")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乳乊") (ℓ "乊乶")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨云") (ℓ "云丨乎亐")
                        wleaf
                      )
                      (ℓ "亊並乕並") (ℓ "並乕並亊")
                      (wnode
                        wleaf
                        (ℓ "乥亯") (ℓ "享乥")
                        wleaf
                      )
                    )
                    (ℓ "二亙交") (ℓ "亙二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亦") (ℓ "亦丬亚")
                        wleaf
                      )
                      (ℓ "亘乤亙") (ℓ "亙亘")
                      wleaf
                    )
                  )
                  (ℓ "並丱丱") (ℓ "並")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏买") (ℓ "买乏")
                        wleaf
                      )
                      (ℓ "亱並亊並") (ℓ "並亊並亱")
                      (wnode
                        wleaf
                        (ℓ "互亚亦") (ℓ "亦互")
                        wleaf
                      )
                    )
                    (ℓ "丝东") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "为二为")
                        wleaf
                      )
                      (ℓ "亦亐亐") (ℓ "亦")
                      wleaf
                    )
                  )
                )
                (ℓ "丫亓") (ℓ "亓丫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亇交並") (ℓ "並交丘亇丢交")
                        wleaf
                      )
                      (ℓ "乖世") (ℓ "世乖")
                      (wnode
                        wleaf
                        (ℓ "乶亏亓") (ℓ "亓乶")
                        wleaf
                      )
                    )
                    (ℓ "上丰") (ℓ "业丯业")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亚") (ℓ "亚乒亏")
                        wleaf
                      )
                      (ℓ "义交产") (ℓ "产交")
                      wleaf
                    )
                  )
                  (ℓ "乢") (ℓ "亭乇乢亰亭么亭乇亭么")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "丨乜丩乜乇")
                        wleaf
                      )
                      (ℓ "乹亪") (ℓ "亪乹")
                      wleaf
                    )
                    (ℓ "交义") (ℓ "产交产")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏些乎些乏") (ℓ "些乎些乏乏")
                        wleaf
                      )
                      (ℓ "么亙") (ℓ "亙么")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "乩乊") (ℓ "乊乕")
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄云") (ℓ "云乄")
                        wleaf
                      )
                      (ℓ "产享享") (ℓ "产")
                      (wnode
                        wleaf
                        (ℓ "书些互乇互么") (ℓ "互乇互么书些")
                        wleaf
                      )
                    )
                    (ℓ "京书") (ℓ "书亨京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊亰亊丢亇亰亇丢") (ℓ "亲亱")
                        wleaf
                      )
                      (ℓ "亘丱") (ℓ "书亘书")
                      wleaf
                    )
                  )
                  (ℓ "乥亚") (ℓ "些乥")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "争亨亨") (ℓ "争")
                        wleaf
                      )
                      (ℓ "亐乇") (ℓ "乇亐")
                      (wnode
                        wleaf
                        (ℓ "亨乑") (ℓ "乑亰")
                        wleaf
                      )
                    )
                    (ℓ "丌乲") (ℓ "丠乱丠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞乩乶乪乶乹丟") (ℓ "亲")
                        wleaf
                      )
                      (ℓ "丰乏") (ℓ "乏丰")
                      wleaf
                    )
                  )
                )
                (ℓ "亃乊") (ℓ "乊了")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乾亨丠") (ℓ "丠亨两乾东亨")
                        wleaf
                      )
                      (ℓ "亊並乩並") (ℓ "並乩並亊")
                      (wnode
                        wleaf
                        (ℓ "两乎亃乏亃乹严") (ℓ "亯")
                        wleaf
                      )
                    )
                    (ℓ "亐亍交") (ℓ "亍亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄亚") (ℓ "亚乄亦")
                        wleaf
                      )
                      (ℓ "亰京亰京亰") (ℓ "亰")
                      wleaf
                    )
                  )
                  (ℓ "亦亪") (ℓ "亪亦")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乪") (ℓ "乪京")
                        wleaf
                      )
                      (ℓ "並丢") (ℓ "一丣並")
                      (wnode
                        wleaf
                        (ℓ "交亏亐") (ℓ "亏亐交亐")
                        wleaf
                      )
                    )
                    (ℓ "两亰严") (ℓ "亳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐") (ℓ "之亐之")
                        wleaf
                      )
                      (ℓ "交亦") (ℓ "亦乐交")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "京乊") (ℓ "乊亰")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇乹") (ℓ "乹亇")
                        wleaf
                      )
                      (ℓ "丢並丢並") (ℓ "並丢並丢")
                      (wnode
                        wleaf
                        (ℓ "中与主与") (ℓ "与主与中")
                        wleaf
                      )
                    )
                    (ℓ "亰") (ℓ "乩乽乪乽乢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐乜交") (ℓ "乜亐")
                        wleaf
                      )
                      (ℓ "交亪") (ℓ "亪交京")
                      wleaf
                    )
                  )
                  (ℓ "二业个") (ℓ "业二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亲亨") (ℓ "亲京")
                        wleaf
                      )
                      (ℓ "之也之") (ℓ "乊")
                      (wnode
                        wleaf
                        (ℓ "乎乪") (ℓ "乪乎")
                        wleaf
                      )
                    )
                    (ℓ "亏亏") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "上与上与") (ℓ "与上与上")
                        wleaf
                      )
                      (ℓ "亰乻") (ℓ "亱亰亱")
                      wleaf
                    )
                  )
                )
                (ℓ "二乊") (ℓ "乊二")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乼亩") (ℓ "亥乼")
                        wleaf
                      )
                      (ℓ "亘交") (ℓ "交亘")
                      (wnode
                        wleaf
                        (ℓ "书亏") (ℓ "亏亓书")
                        wleaf
                      )
                    )
                    (ℓ "丩么二么义二") (ℓ "丩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏亓产") (ℓ "产亏")
                        wleaf
                      )
                      (ℓ "丞乇乳么乳乢丟") (ℓ "产")
                      wleaf
                    )
                  )
                  (ℓ "云云") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乗亮") (ℓ "亮京")
                        wleaf
                      )
                      (ℓ "丒亄丢亭乇亭么") (ℓ "亭乇亭么丒亄丢")
                      wleaf
                    )
                    (ℓ "串串") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎亳") (ℓ "亳乎")
                        wleaf
                      )
                      (ℓ "丯並") (ℓ "並丯")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "乽乥") (ℓ "乥乭")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩丢") (ℓ "丢乩")
                        wleaf
                      )
                      (ℓ "亨享") (ℓ "享义亨")
                      (wnode
                        wleaf
                        (ℓ "些乎些乏一下") (ℓ "一下些乎些乏")
                        wleaf
                      )
                    )
                    (ℓ "亰") (ℓ "乳亰乳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亨亇丢") (ℓ "亪")
                        wleaf
                      )
                      (ℓ "丷些") (ℓ "些丷丰亘")
                      wleaf
                    )
                  )
                  (ℓ "丘乇丬么丬丯丘一") (ℓ "丘乇丳么丳丨丘一")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亊交並") (ℓ "並交丞亊丢交")
                        wleaf
                      )
                      (ℓ "亊並亇並") (ℓ "並亇並亊")
                      (wnode
                        wleaf
                        (ℓ "乩乢亰乢乤亰") (ℓ "乩")
                        wleaf
                      )
                    )
                    (ℓ "乭了乭") (ℓ "乬")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "东乼") (ℓ "乼丢")
                        wleaf
                      )
                      (ℓ "买亦") (ℓ "亦买")
                      wleaf
                    )
                  )
                )
                (ℓ "乊亳") (ℓ "亯乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕亄乕亄乕亄") (ℓ "丢丢丢")
                        wleaf
                      )
                      (ℓ "亲乎亲乏並乹並") (ℓ "並乹並亲乎亲乏")
                      (wnode
                        wleaf
                        (ℓ "互亚亚") (ℓ "互")
                        wleaf
                      )
                    )
                    (ℓ "二二") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘亮") (ℓ "亮丘")
                        wleaf
                      )
                      (ℓ "乙产产") (ℓ "乙")
                      wleaf
                    )
                  )
                  (ℓ "书亲") (ℓ "亲书")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乣") (ℓ "乣京")
                        wleaf
                      )
                      (ℓ "丘亇丢並") (ℓ "並亇")
                      wleaf
                    )
                    (ℓ "丷么") (ℓ "么丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰") (ℓ "乤亰乤")
                        wleaf
                      )
                      (ℓ "丷乇") (ℓ "乇丷")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乫乊") (ℓ "乊乗")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丷丶") []
                        wleaf
                      )
                      (ℓ "乩並乕並") (ℓ "並乕並乩")
                      (wnode
                        wleaf
                        (ℓ "享亯") (ℓ "亯享")
                        wleaf
                      )
                    )
                    (ℓ "亘乤亙亘") (ℓ "亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交京亱") (ℓ "亱交")
                        wleaf
                      )
                      (ℓ "丰乣亘乣乤亘") (ℓ "丰")
                      wleaf
                    )
                  )
                  (ℓ "交交") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为为") []
                        wleaf
                      )
                      (ℓ "亊並亊並") (ℓ "並亊並亊")
                      (wnode
                        wleaf
                        (ℓ "亦京京") (ℓ "亦")
                        wleaf
                      )
                    )
                    (ℓ "丩东亓丝") (ℓ "亓亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "与上与上") (ℓ "一")
                        wleaf
                      )
                      (ℓ "二个亏") (ℓ "亏二")
                      wleaf
                    )
                  )
                )
                (ℓ "之丫") (ℓ "丫丳")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交乕乕") (ℓ "乕乕交")
                        wleaf
                      )
                      (ℓ "乖世亪丗") (ℓ "亪亨")
                      (wnode
                        wleaf
                        (ℓ "乩亲") (ℓ "亲乩")
                        wleaf
                      )
                    )
                    (ℓ "丱义义") (ℓ "丱")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞乕乽乖乽乎丟") (ℓ "亮")
                        wleaf
                      )
                      (ℓ "乏产") (ℓ "产乏么交")
                      wleaf
                    )
                  )
                  (ℓ "亰") (ℓ "乹乭乺乭乢")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二丢") (ℓ "丢二")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "丯买丰买乢")
                      wleaf
                    )
                    (ℓ "丨产") (ℓ "产丨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些与") (ℓ "与书些")
                        wleaf
                      )
                      (ℓ "丒乹乙乺乙乎专") (ℓ "亭")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乕乊") (ℓ "乊乩")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亭乇") (ℓ "亭乇亰")
                        wleaf
                      )
                      (ℓ "亓产") (ℓ "产亓")
                      (wnode
                        wleaf
                        (ℓ "亘互乇") (ℓ "互乇亘")
                        wleaf
                      )
                    )
                    (ℓ "二") (ℓ "亐亓乤亓亐乤")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交丢亨亨亨亲乎亨亨亲乏") (ℓ "丢亨亨亨亲乎亨亨亲乏交")
                        wleaf
                      )
                      (ℓ "丞京丟") (ℓ "亮")
                      wleaf
                    )
                  )
                  (ℓ "京乼") (ℓ "乼京")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘云交") (ℓ "云亘")
                        wleaf
                      )
                      (ℓ "亨交亨交亨") (ℓ "亨")
                      (wnode
                        wleaf
                        (ℓ "乳享") (ℓ "享乳亳")
                        wleaf
                      )
                    )
                    (ℓ "丰丐于丑") (ℓ "于二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亦亏亓") (ℓ "亓亦")
                        wleaf
                      )
                      (ℓ "丶云") (ℓ "云丶乎亐")
                      wleaf
                    )
                  )
                )
                (ℓ "乜丫") (ℓ "丫也")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也些些") (ℓ "也")
                        wleaf
                      )
                      (ℓ "乕並乹並") (ℓ "並乹並乕")
                      (wnode
                        wleaf
                        (ℓ "乥享") (ℓ "亯乥")
                        wleaf
                      )
                    )
                    (ℓ "乳亘亘") (ℓ "乳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬产") (ℓ "产丬些")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "交亦丱亦交丱")
                      wleaf
                    )
                  )
                  (ℓ "二于乐于二乐") (ℓ "亘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘产二") (ℓ "产亘")
                        wleaf
                      )
                      (ℓ "东乺並") (ℓ "並乹")
                      wleaf
                    )
                    (ℓ "乇亳") (ℓ "亳乇")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亯") (ℓ "亯京乐")
                        wleaf
                      )
                      (ℓ "交亨亨亮") (ℓ "亨亮交")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乊亮") (ℓ "亲乊")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乤亊乤") (ℓ "亊亰")
                        wleaf
                      )
                      (ℓ "並丢並") (ℓ "一丣")
                      (wnode
                        wleaf
                        (ℓ "丞主上些乎些乏") (ℓ "些乎些乏丞主上")
                        wleaf
                      )
                    )
                    (ℓ "亰乙") (ℓ "乙交亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交丳亐") (ℓ "丳交")
                        wleaf
                      )
                      (ℓ "丷乶") (ℓ "乶丷")
                      wleaf
                    )
                  )
                  (ℓ "交乩") (ℓ "乩交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐丨") (ℓ "丨亐")
                        wleaf
                      )
                      (ℓ "亲乎亲乏並亇並") (ℓ "並亇並亲乎亲乏")
                      (wnode
                        wleaf
                        (ℓ "丙亯") (ℓ "亯丙")
                        wleaf
                      )
                    )
                    (ℓ "乎亱") (ℓ "亱乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨与") (ℓ "与丐丩")
                        wleaf
                      )
                      (ℓ "乳亱") (ℓ "亱乳")
                      wleaf
                    )
                  )
                )
                (ℓ "丒丫") (ℓ "丫丌")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乽亪") (ℓ "亪乽亦")
                        wleaf
                      )
                      (ℓ "亘乇") (ℓ "乇亘")
                      (wnode
                        wleaf
                        (ℓ "乺乪亰乪乫亰") (ℓ "乺")
                        wleaf
                      )
                    )
                    (ℓ "下丨") (ℓ "且丩且")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亨亨") (ℓ "乒")
                        wleaf
                      )
                      (ℓ "乊些") (ℓ "亓乊")
                      wleaf
                    )
                  )
                  (ℓ "乳亭") (ℓ "亭乳")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰丘") (ℓ "丘亱亰亰")
                        wleaf
                      )
                      (ℓ "京亮") (ℓ "亮京乗")
                      wleaf
                    )
                    (ℓ "亐云丱云亐丱") (ℓ "交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏亳") (ℓ "亳乏")
                        wleaf
                      )
                      (ℓ "乎亲乎亲乏") (ℓ "亲乎亲乏乎")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "乣乊") (ℓ "乊乏")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕乹") (ℓ "乹乕")
                        wleaf
                      )
                      (ℓ "乽乽") []
                      (wnode
                        wleaf
                        (ℓ "亐") (ℓ "乶亐乶")
                        wleaf
                      )
                    )
                    (ℓ "二乑") (ℓ "乑亘")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亩亲产") (ℓ "产亩")
                        wleaf
                      )
                      (ℓ "亘丯") (ℓ "丯亘")
                      wleaf
                    )
                  )
                  (ℓ "不丌") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "之亮亮") (ℓ "之")
                        wleaf
                      )
                      (ℓ "亘乏") (ℓ "乏亘")
                      (wnode
                        wleaf
                        (ℓ "之亏与") (ℓ "与亏")
                        wleaf
                      )
                    )
                    (ℓ "亰亭") (ℓ "亭亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹与") (ℓ "与乹")
                        wleaf
                      )
                      (ℓ "丹亦") (ℓ "亏丹")
                      wleaf
                    )
                  )
                )
                (ℓ "乊乘") (ℓ "乬乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩亲乎亲乏") (ℓ "亲乎亲乏乩")
                        wleaf
                      )
                      (ℓ "乩並亄並") (ℓ "並亄並乩")
                      (wnode
                        wleaf
                        (ℓ "乇乹") (ℓ "乹乇")
                        wleaf
                      )
                    )
                    (ℓ "乇亍") (ℓ "亍乇")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亲亱亲亲亱亲") []
                        wleaf
                      )
                      (ℓ "丯产") (ℓ "产丯")
                      wleaf
                    )
                  )
                  (ℓ "乇亙") (ℓ "亙乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了京京") (ℓ "了")
                        wleaf
                      )
                      (ℓ "东乺亲乎亲乏") (ℓ "亲乎亲乏东乺")
                      wleaf
                    )
                    (ℓ "亐") (ℓ "丶乄丷乄乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞丶书丷书丯丟") (ℓ "些")
                        wleaf
                      )
                      (ℓ "乑亙") (ℓ "亍乑")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乤乘") (ℓ "乘乤")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亍产") (ℓ "产亍")
                        wleaf
                      )
                      (ℓ "丐乖亲乎亲乏") (ℓ "亲乎亲乏丐乖")
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "丬亘丬")
                        wleaf
                      )
                    )
                    (ℓ "京乭") (ℓ "乭交京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交产乻产交乻") (ℓ "亨")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "乩乶乪乶乹")
                      wleaf
                    )
                  )
                  (ℓ "乒亮") (ℓ "亮乒")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘产") (ℓ "产亘二")
                        wleaf
                      )
                      (ℓ "亐书二") (ℓ "书亐")
                      (wnode
                        wleaf
                        (ℓ "上亦") (ℓ "亦上")
                        wleaf
                      )
                    )
                    (ℓ "交亲") (ℓ "亲交亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交为") (ℓ "为二交")
                        wleaf
                      )
                      (ℓ "亰亦京") (ℓ "亦亰")
                      wleaf
                    )
                  )
                )
                (ℓ "丌乇丬么丬丯丌一") (ℓ "丌乇丬么丬丯丌丂")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乽交") (ℓ "乽亨")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "乢为乣为丯")
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "乳亘乳")
                        wleaf
                      )
                    )
                    (ℓ "二为") (ℓ "为二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "亰京亰")
                        wleaf
                      )
                      (ℓ "京亪") (ℓ "亪京")
                      wleaf
                    )
                  )
                  (ℓ "乶云云") (ℓ "乶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亲") (ℓ "亲京亨")
                        wleaf
                      )
                      (ℓ "交乕") (ℓ "乕交")
                      wleaf
                    )
                    (ℓ "丳乜丳") (ℓ "串")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亳与上与") (ℓ "与上与亳")
                        wleaf
                      )
                      (ℓ "京乶") (ℓ "乶京")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    [] []
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乥于") (ℓ "互乥")
                        wleaf
                      )
                      (ℓ "丸产") (ℓ "产丸二")
                      (wnode
                        wleaf
                        (ℓ "互乇互么一下") (ℓ "一下互乇互么")
                        wleaf
                      )
                    )
                    (ℓ "亨") (ℓ "乩之乪之乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乐些") (ℓ "些乐二")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "乗亨乗")
                      wleaf
                    )
                  )
                  (ℓ "乺乼") (ℓ "乼乺")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乎") (ℓ "乎亨")
                        wleaf
                      )
                      (ℓ "亘亚") (ℓ "亚亘丸")
                      (wnode
                        wleaf
                        (ℓ "乒享享") (ℓ "乒")
                        wleaf
                      )
                    )
                    (ℓ "买交交") (ℓ "买")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亨") (ℓ "产京产")
                        wleaf
                      )
                      (ℓ "乎並") (ℓ "並乎")
                      wleaf
                    )
                  )
                )
                (ℓ "丞乥") (ℓ "乥丘")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丠个个") (ℓ "丠")
                        wleaf
                      )
                      (ℓ "乕並乩並") (ℓ "並乩並乕")
                      (wnode
                        wleaf
                        (ℓ "亘乄") (ℓ "乄交亘")
                        wleaf
                      )
                    )
                    (ℓ "京交京交京") (ℓ "京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亰亪") (ℓ "亪亰")
                        wleaf
                      )
                      (ℓ "乳亙") (ℓ "亙乳")
                      wleaf
                    )
                  )
                  (ℓ "亦亪亮") (ℓ "亮亦")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乬") (ℓ "乬交")
                        wleaf
                      )
                      (ℓ "二亐") (ℓ "亐二")
                      (wnode
                        wleaf
                        (ℓ "之亯亯") (ℓ "之")
                        wleaf
                      )
                    )
                    (ℓ "亐之") (ℓ "之亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "两京严") (ℓ "亯")
                        wleaf
                      )
                      (ℓ "京亰") (ℓ "亰京")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乗乊") (ℓ "乊乫")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕亭乇亭么") (ℓ "亭乇亭么乕")
                        wleaf
                      )
                      (ℓ "争亲") (ℓ "亲争")
                      (wnode
                        wleaf
                        (ℓ "二亐二亐二") (ℓ "二")
                        wleaf
                      )
                    )
                    (ℓ "二") (ℓ "亘些乐些亘乐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "专些") (ℓ "些专")
                        wleaf
                      )
                      (ℓ "丶些") (ℓ "些丶丯亘")
                      wleaf
                    )
                  )
                  (ℓ "二亍") (ℓ "亍二义")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亮") (ℓ "亮也亲")
                        wleaf
                      )
                      (ℓ "之亐亐") (ℓ "之")
                      (wnode
                        wleaf
                        (ℓ "亏与") (ℓ "与之亏")
                        wleaf
                      )
                    )
                    (ℓ "丘二丙") (ℓ "亏")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "中与上与") (ℓ "与上与中")
                        wleaf
                      )
                      (ℓ "丹丹") []
                      wleaf
                    )
                  )
                )
                (ℓ "乊乑") (ℓ "乥乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "争亦") (ℓ "亦争亪")
                        wleaf
                      )
                      (ℓ "亇並亄並") (ℓ "並亄並亇")
                      (wnode
                        wleaf
                        (ℓ "丵") (ℓ "丯丙丯丘丯")
                        wleaf
                      )
                    )
                    (ℓ "么亍") (ℓ "亍么")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘乹乭乺乭乢丙") (ℓ "亱")
                        wleaf
                      )
                      (ℓ "乘产") (ℓ "亲乘")
                      wleaf
                    )
                  )
                  (ℓ "乇") (ℓ "亲乇乎亨亲乏亲乎亲乏")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亄") (ℓ "乐亄乐京")
                        wleaf
                      )
                      (ℓ "丘亇丢亲乎亲乏") (ℓ "亲乎亲乏丘亇丢")
                      wleaf
                    )
                    (ℓ "乜丳乜") (ℓ "串")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二乎些") (ℓ "乎些二")
                        wleaf
                      )
                      (ℓ "二乏") (ℓ "乏二")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "为丫") (ℓ "丫乒")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买云") (ℓ "云买")
                        wleaf
                      )
                      (ℓ "交串") (ℓ "串亐")
                      (wnode
                        wleaf
                        (ℓ "乽亯") (ℓ "亯乽")
                        wleaf
                      )
                    )
                    (ℓ "亨") (ℓ "乒亨乒")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亭乇亭么亇亨亇丢亭乇亰亭么交亇亨亇交丢") (ℓ "亲乎亲乏亇亰亇丢亲乎亨亲乏交亇亰亇交丢")
                        wleaf
                      )
                      (ℓ "丰东些丝") (ℓ "些亘")
                      wleaf
                    )
                  )
                  (ℓ "乊享") (ℓ "享乊")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亘亘") (ℓ "也")
                        wleaf
                      )
                      (ℓ "乕並亇並") (ℓ "並亇並乕")
                      (wnode
                        wleaf
                        (ℓ "乑享") (ℓ "亳乑")
                        wleaf
                      )
                    )
                    (ℓ "丰丐") (ℓ "丐丰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "上丫") (ℓ "丫丐")
                        wleaf
                      )
                      (ℓ "交乐亦") (ℓ "亦交")
                      wleaf
                    )
                  )
                )
                (ℓ "买乊") (ℓ "乊买")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩乩乩乩") []
                        wleaf
                      )
                      (ℓ "亄並乹並") (ℓ "並乹並亄")
                      (wnode
                        wleaf
                        (ℓ "京亯") (ℓ "亯乐京")
                        wleaf
                      )
                    )
                    (ℓ "亰乳") (ℓ "乳亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亮") (ℓ "亮亨亰")
                        wleaf
                      )
                      (ℓ "亃亲") (ℓ "亲亃")
                      wleaf
                    )
                  )
                  (ℓ "並个个") (ℓ "並")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乬亥") (ℓ "亭乬")
                        wleaf
                      )
                      (ℓ "丒亄丢並") (ℓ "並亄")
                      wleaf
                    )
                    (ℓ "交亍") (ℓ "亍交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘临上些乎些乏") (ℓ "些乎些乏丘临上")
                        wleaf
                      )
                      (ℓ "乳乶亦") (ℓ "亦乳")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乖乥") (ℓ "乥乖")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乤亊乤乤") (ℓ "乤亊")
                        wleaf
                      )
                      (ℓ "亘丬") (ℓ "丬亘")
                      (wnode
                        wleaf
                        (ℓ "临与中与") (ℓ "与中与临")
                        wleaf
                      )
                    )
                    (ℓ "亰交亰交亰") (ℓ "亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亏") (ℓ "亏交亐")
                        wleaf
                      )
                      (ℓ "丯乥") (ℓ "乥丶")
                      wleaf
                    )
                  )
                  (ℓ "乏世亦丗") (ℓ "亦交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎亓") (ℓ "亓乎丨亐")
                        wleaf
                      )
                      (ℓ "乕並亊並") (ℓ "並亊並乕")
                      (wnode
                        wleaf
                        (ℓ "互乇互么亏互乇亘互么亏亐些亚些些乎些乏些二亚亐些二") []
                        wleaf
                      )
                    )
                    (ℓ "亰乏") (ℓ "乏亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乼並") (ℓ "丠乼")
                        wleaf
                      )
                      (ℓ "乙亦") (ℓ "亦乙")
                      wleaf
                    )
                  )
                )
                (ℓ "么乊") (ℓ "乊么")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乽亦亦") (ℓ "乽")
                        wleaf
                      )
                      (ℓ "丘亨丙") (ℓ "亪")
                      (wnode
                        wleaf
                        (ℓ "乺乪亰书") (ℓ "书乺")
                        wleaf
                      )
                    )
                    (ℓ "丯亍") (ℓ "亍丯乇二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亚亚") (ℓ "乳")
                        wleaf
                      )
                      (ℓ "书产") (ℓ "产书")
                      wleaf
                    )
                  )
                  (ℓ "並乢交亰") (ℓ "並乳乳乢交亰")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘亇丢") (ℓ "丘亱亰乤亇乤丢")
                        wleaf
                      )
                      (ℓ "交亮") (ℓ "亮交亨")
                      wleaf
                    )
                    (ℓ "亰产") (ℓ "产亨亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "书些与") (ℓ "与些")
                        wleaf
                      )
                      (ℓ "交乽") (ℓ "乽交")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乹乥") (ℓ "乥乩")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乇亭") (ℓ "乇亭亰")
                        wleaf
                      )
                      (ℓ "亐个亓亐") (ℓ "亓")
                      (wnode
                        wleaf
                        (ℓ "么亯") (ℓ "亯么")
                        wleaf
                      )
                    )
                    (ℓ "亐乥") (ℓ "乥二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亩亪亭乇亭么交亇亨亇丢亄亨亄交丢") (ℓ "亲亱亲乎亲乏交亇亰亇丢亊亰亊交丢")
                        wleaf
                      )
                      (ℓ "丘乇亃么亃乩丙") (ℓ "亪")
                      wleaf
                    )
                  )
                  (ℓ "丫亚") (ℓ "亦丫")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亄") (ℓ "义亄义亨")
                        wleaf
                      )
                      (ℓ "交") (ℓ "乽交乽")
                      (wnode
                        wleaf
                        (ℓ "乑亪") (ℓ "亱乑")
                        wleaf
                      )
                    )
                    (ℓ "京么") (ℓ "么京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇") (ℓ "亲乎乇亨亲乏亲乎亲乏")
                        wleaf
                      )
                      (ℓ "丷云") (ℓ "云丷乏亐")
                      wleaf
                    )
                  )
                )
                (ℓ "乊乬") (ℓ "乘乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乾东亨") (ℓ "亨乿亨")
                        wleaf
                      )
                      (ℓ "亮並乩並") (ℓ "並乩並亮")
                      (wnode
                        wleaf
                        (ℓ "亯交交") (ℓ "亯")
                        wleaf
                      )
                    )
                    (ℓ "二丷") (ℓ "丷二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄亦亦") (ℓ "乄")
                        wleaf
                      )
                      (ℓ "亘乊") (ℓ "乊亐")
                      wleaf
                    )
                  )
                  (ℓ "丌亘不") (ℓ "亙")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩些") (ℓ "些丩")
                        wleaf
                      )
                      (ℓ "丐乖亦") (ℓ "亦丐乖")
                      (wnode
                        wleaf
                        (ℓ "书些亏") (ℓ "亏书些")
                        wleaf
                      )
                    )
                    (ℓ "丣丢") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘之") (ℓ "之亐亘")
                        wleaf
                      )
                      (ℓ "么亦") (ℓ "亦么乏交")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丘乊") (ℓ "乊丒")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亊") (ℓ "亊亄")
                        wleaf
                      )
                      (ℓ "乹並丢並") (ℓ "並丢並乹")
                      (wnode
                        wleaf
                        (ℓ "亨丞") (ℓ "丞亨")
                        wleaf
                      )
                    )
                    (ℓ "二云交") (ℓ "云二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交为二") (ℓ "为交")
                        wleaf
                      )
                      (ℓ "乹亦") (ℓ "亦乹")
                      wleaf
                    )
                  )
                  (ℓ "二个") (ℓ "个二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亓") (ℓ "亓个亐")
                        wleaf
                      )
                      (ℓ "亰之") (ℓ "之京亰")
                      (wnode
                        wleaf
                        (ℓ "临二临上") (ℓ "亏")
                        wleaf
                      )
                    )
                    (ℓ "交乙") (ℓ "乙交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "上与") (ℓ "与一下")
                        wleaf
                      )
                      (ℓ "亰亱") (ℓ "亱亰乻")
                      wleaf
                    )
                  )
                )
                (ℓ "丫于") (ℓ "亍丫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "义亚") (ℓ "亚义亐")
                        wleaf
                      )
                      (ℓ "交乄") (ℓ "乄交")
                      (wnode
                        wleaf
                        (ℓ "丘乇丬么丬丯丙") (ℓ "亏")
                        wleaf
                      )
                    )
                    (ℓ "个义义") (ℓ "个")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇亓") (ℓ "亓乇")
                        wleaf
                      )
                      (ℓ "之云") (ℓ "云之")
                      wleaf
                    )
                  )
                  (ℓ "丱云") (ℓ "云丱交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亓二") (ℓ "亓交")
                        wleaf
                      )
                      (ℓ "丞亊丢亭乇亭么") (ℓ "亭乇亭么丞亊丢")
                      wleaf
                    )
                    (ℓ "么东产丝") (ℓ "产交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇些乎些乏") (ℓ "些乎些乏乇")
                        wleaf
                      )
                      (ℓ "亨亲乎") (ℓ "亲乎亨")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丯丫") (ℓ "丫乇")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇丢") (ℓ "丢亇")
                        wleaf
                      )
                      (ℓ "丳产") (ℓ "产丳亓")
                      (wnode
                        wleaf
                        (ℓ "临与主与") (ℓ "与主与临")
                        wleaf
                      )
                    )
                    (ℓ "亨乒") (ℓ "乒亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也些") (ℓ "些也")
                        wleaf
                      )
                      (ℓ "丰些") (ℓ "些丰")
                      wleaf
                    )
                  )
                  (ℓ "主丫") (ℓ "丫乓")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交乹乹") (ℓ "乹乹交")
                        wleaf
                      )
                      (ℓ "予") (ℓ "乩丙乩丘乩")
                      (wnode
                        wleaf
                        (ℓ "乪乣亰乣乤亰") (ℓ "乪")
                        wleaf
                      )
                    )
                    (ℓ "交亭") (ℓ "亭交亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乫亦") (ℓ "亦乫京")
                        wleaf
                      )
                      (ℓ "乄亦") (ℓ "亦乄")
                      wleaf
                    )
                  )
                )
                (ℓ "乱乊") (ℓ "乊乱")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        [] []
                        wleaf
                      )
                      (ℓ "不亘") (ℓ "亙不")
                      (wnode
                        wleaf
                        (ℓ "乙乒亯") (ℓ "亯乒")
                        wleaf
                      )
                    )
                    (ℓ "亐互义互亐义") (ℓ "亘")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京产亨") (ℓ "产京")
                        wleaf
                      )
                      (ℓ "亰乘") (ℓ "乘交")
                      wleaf
                    )
                  )
                  (ℓ "並乇交亨") (ℓ "並书书乇交亨")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乭交") (ℓ "乭京")
                        wleaf
                      )
                      (ℓ "亇並") (ℓ "並丘亇丢")
                      wleaf
                    )
                    (ℓ "乽享") (ℓ "享乽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亳") (ℓ "亳京交")
                        wleaf
                      )
                      (ℓ "么並") (ℓ "並么")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乥乬") (ℓ "乼乥")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丸二亍丸亍二二亍丸亍二丸") []
                        wleaf
                      )
                      (ℓ "亇並乕並") (ℓ "並乕並亇")
                      (wnode
                        wleaf
                        (ℓ "亨乥") (ℓ "乥京")
                        wleaf
                      )
                    )
                    (ℓ "京") (ℓ "了京了")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亦") (ℓ "亦亨京")
                        wleaf
                      )
                      (ℓ "丯乢亘乢乤亘") (ℓ "丯")
                      wleaf
                    )
                  )
                  (ℓ "亐") (ℓ "乎丬乏丬丶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎买") (ℓ "买乎")
                        wleaf
                      )
                      (ℓ "交亏亐") (ℓ "亏交")
                      (wnode
                        wleaf
                        (ℓ "交与") (ℓ "与交")
                        wleaf
                      )
                    )
                    (ℓ "乪东") (ℓ "东乪")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亄丢") []
                        wleaf
                      )
                      (ℓ "丘乎也乏也乢丙") (ℓ "亦")
                      wleaf
                    )
                  )
                )
                (ℓ "丘乇丬么丬丯丘一") (ℓ "丘乇丬么丬丯丘丂")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亇交交") (ℓ "交亇")
                        wleaf
                      )
                      (ℓ "丷世") (ℓ "世丷")
                      (wnode
                        wleaf
                        (ℓ "乹乶") (ℓ "乶乹")
                        wleaf
                      )
                    )
                    (ℓ "乞") (ℓ "丯不丯丌丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亰亰") (ℓ "乳")
                        wleaf
                      )
                      (ℓ "丘乩之乪之乕丙") (ℓ "亪")
                      wleaf
                    )
                  )
                  (ℓ "亰亭乇乢亰") (ℓ "亭乇乢")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐些") (ℓ "些亐二")
                        wleaf
                      )
                      (ℓ "丟亪") (ℓ "亪丟")
                      wleaf
                    )
                    (ℓ "交义产") (ℓ "产交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏与") (ℓ "与乏")
                        wleaf
                      )
                      (ℓ "么亲乎亲乏") (ℓ "亲乎亲乏么")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "乼乼") []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄乒云") (ℓ "云乒")
                        wleaf
                      )
                      (ℓ "享亳") (ℓ "亳享")
                      (wnode
                        wleaf
                        (ℓ "亘乇互") (ℓ "乇互亘")
                        wleaf
                      )
                    )
                    (ℓ "亨书") (ℓ "书亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎亍") (ℓ "亍乎")
                        wleaf
                      )
                      (ℓ "亘丱书") (ℓ "书亘")
                      wleaf
                    )
                  )
                  (ℓ "亘乥") (ℓ "乥亘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交争亨") (ℓ "争交")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "乕乭乖乭乇")
                      (wnode
                        wleaf
                        (ℓ "亘二亘二亘") (ℓ "亘")
                        wleaf
                      )
                    )
                    (ℓ "下丶") (ℓ "丠丷丠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丐") (ℓ "並乕並乕")
                        wleaf
                      )
                      (ℓ "乏並") (ℓ "並乏")
                      wleaf
                    )
                  )
                )
                (ℓ "丞乢之乣之乎丞一") (ℓ "丞乢之乣之乎丞丂")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "两乾东丠") (ℓ "丠乾")
                        wleaf
                      )
                      (ℓ "亇並乩並") (ℓ "並乩並亇")
                      (wnode
                        wleaf
                        (ℓ "交亘交亘交") (ℓ "交")
                        wleaf
                      )
                    )
                    (ℓ "亐乢") (ℓ "乢亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亚") (ℓ "亚丬")
                        wleaf
                      )
                      (ℓ "亰也") (ℓ "也亰")
                      wleaf
                    )
                  )
                  (ℓ "丶亦") (ℓ "亦丶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乩") (ℓ "乩京")
                        wleaf
                      )
                      (ℓ "亭乇亭么並亊並") (ℓ "並亊並亭乇亭么")
                      (wnode
                        wleaf
                        (ℓ "也亳亳") (ℓ "也")
                        wleaf
                      )
                    )
                    (ℓ "亰乕") (ℓ "乕亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "中与临与") (ℓ "与临与中")
                        wleaf
                      )
                      (ℓ "乇亦") (ℓ "亦乇乎交")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乤乊") (ℓ "乊乐")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄乹") (ℓ "乹亄")
                        wleaf
                      )
                      (ℓ "乼享") (ℓ "产乼")
                      (wnode
                        wleaf
                        (ℓ "互乇互么与主与") (ℓ "与主与互乇互么")
                        wleaf
                      )
                    )
                    (ℓ "二亏乤亏二乤") (ℓ "亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亰亇丢") (ℓ "亱")
                        wleaf
                      )
                      (ℓ "京亮") (ℓ "亮乗京")
                      wleaf
                    )
                  )
                  (ℓ "二亍") (ℓ "亍义二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐个") (ℓ "为亐为")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "也亰也")
                      (wnode
                        wleaf
                        (ℓ "乪与") (ℓ "与乪")
                        wleaf
                      )
                    )
                    (ℓ "亱亱") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "中与中与") (ℓ "与中与中")
                        wleaf
                      )
                      (ℓ "亰乻亱") (ℓ "亱亰")
                      wleaf
                    )
                  )
                )
                (ℓ "丫乊") (ℓ "串丫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交乼") (ℓ "乼亨")
                        wleaf
                      )
                      (ℓ "交丬亘") (ℓ "丬交")
                      (wnode
                        wleaf
                        (ℓ "亐交亏") (ℓ "亏交")
                        wleaf
                      )
                    )
                    (ℓ "丩亍") (ℓ "亍丩么二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞丨乳丩乳丶丟") (ℓ "亓")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "个亐个")
                      wleaf
                    )
                  )
                  (ℓ "乏乪") (ℓ "乪乏")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒些") (ℓ "些丒")
                        wleaf
                      )
                      (ℓ "东乺亭乇亭么") (ℓ "亭乇亭么东乺")
                      wleaf
                    )
                    (ℓ "交亐交亐交") (ℓ "交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒丶乄丷乄乎专") (ℓ "互")
                        wleaf
                      )
                      (ℓ "亪並") (ℓ "並之亪")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "乭乥") (ℓ "乥乽")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕丢") (ℓ "丢乕")
                        wleaf
                      )
                      (ℓ "亨享义") (ℓ "享亨")
                      (wnode
                        wleaf
                        (ℓ "上与临与") (ℓ "与临与上")
                        wleaf
                      )
                    )
                    (ℓ "乳亙亙") (ℓ "乳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乾乿") []
                        wleaf
                      )
                      (ℓ "亮亮") []
                      wleaf
                    )
                  )
                  (ℓ "丫云") (ℓ "互丫")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亊交交") (ℓ "交亊")
                        wleaf
                      )
                      (ℓ "亇並亇並") (ℓ "並亇並亇")
                      (wnode
                        wleaf
                        (ℓ "乢亳") (ℓ "亳乢")
                        wleaf
                      )
                    )
                    (ℓ "二亙") (ℓ "亙二交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "世乥") (ℓ "乥东")
                        wleaf
                      )
                      (ℓ "交乐亦交") (ℓ "亦")
                      wleaf
                    )
                  )
                )
                (ℓ "乊亯") (ℓ "亳乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亊亊") (ℓ "丢丢丢")
                        wleaf
                      )
                      (ℓ "东乺") (ℓ "並乹並")
                      (wnode
                        wleaf
                        (ℓ "互亦") (ℓ "亦互亚")
                        wleaf
                      )
                    )
                    (ℓ "二") (ℓ "义二义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丙亮") (ℓ "亮丙")
                        wleaf
                      )
                      (ℓ "产亲") (ℓ "亲产")
                      wleaf
                    )
                  )
                  (ℓ "乎书") (ℓ "书乇交乎")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘丱") (ℓ "些亘些")
                        wleaf
                      )
                      (ℓ "亇") (ℓ "乪丙乪丘乪")
                      wleaf
                    )
                    (ℓ "么丢享丣") (ℓ "享亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乤") (ℓ "亳亰亳")
                        wleaf
                      )
                      (ℓ "乇並") (ℓ "並乇")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丫亥") (ℓ "亙丫")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亊交亲乎亲乏") (ℓ "亲乎亲乏亊")
                        wleaf
                      )
                      (ℓ "乕並乕並") (ℓ "並乕並乕")
                      (wnode
                        wleaf
                        (ℓ "之亯") (ℓ "亯之")
                        wleaf
                      )
                    )
                    (ℓ "亘亙") (ℓ "亙亘乤")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕亱") (ℓ "亱乕")
                        wleaf
                      )
                      (ℓ "乣亙") (ℓ "亙乣")
                      wleaf
                    )
                  )
                  (ℓ "亦亦") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亲") (ℓ "亲乫亰")
                        wleaf
                      )
                      (ℓ "亇並亊並") (ℓ "並亊並亇")
                      (wnode
                        wleaf
                        (ℓ "丞") (ℓ "与主与主")
                        wleaf
                      )
                    )
                    (ℓ "丟丞") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒") (ℓ "与中与中")
                        wleaf
                      )
                      (ℓ "亃亱亱") (ℓ "亃")
                      wleaf
                    )
                  )
                )
                (ℓ "丒丯乄丰乄乇丒一") (ℓ "丒乇丬么丬丯丒一")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亄交並") (ℓ "並交丒亄丢交")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "丸亘丸")
                      (wnode
                        wleaf
                        (ℓ "乹亲") (ℓ "亲乹乩亰")
                        wleaf
                      )
                    )
                    (ℓ "丱亍") (ℓ "亍丱义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亮") (ℓ "亮亰亨")
                        wleaf
                      )
                      (ℓ "乎乇交乇义交") (ℓ "乎")
                      wleaf
                    )
                  )
                  (ℓ "么云") (ℓ "云么")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢产") (ℓ "产丢")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "亰亲乐亲亰乐")
                      wleaf
                    )
                    (ℓ "丩产") (ℓ "产丩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二书二些") (ℓ "书些")
                        wleaf
                      )
                      (ℓ "乳亭亲乎亲乏") (ℓ "亲乎亲乏乳亭")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乪乥") (ℓ "乥乺")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亰亭乇亰亭么並") (ℓ "亰亭乇亰亭么並交")
                        wleaf
                      )
                      (ℓ "之亓") (ℓ "亓之")
                      (wnode
                        wleaf
                        (ℓ "亘互乇亘互么与交") (ℓ "交亘互乇亘互么与")
                        wleaf
                      )
                    )
                    (ℓ "二丶") (ℓ "丶二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亇交亰交亇交丢亨亨亨亲乎亨亨亲乏交交亇交交亰交交亇") (ℓ "亇交亰交亇交丢亨亨亨亲乎亨亨亲乏交交亇交交亰交交亇交")
                        wleaf
                      )
                      (ℓ "亪亮亮") (ℓ "亪")
                      wleaf
                    )
                  )
                  (ℓ "乥亥") (ℓ "亥乥")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘云") (ℓ "云亘交")
                        wleaf
                      )
                      (ℓ "交争") (ℓ "争亨交")
                      (wnode
                        wleaf
                        (ℓ "享交交") (ℓ "享")
                        wleaf
                      )
                    )
                    (ℓ "专丒") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌上上丌一") (ℓ "与")
                        wleaf
                      )
                      (ℓ "丷乏亐乏乐亐") (ℓ "丷")
                      wleaf
                    )
                  )
                )
                (ℓ "丱丫") (ℓ "丫义")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓些") (ℓ "些亓")
                        wleaf
                      )
                      (ℓ "丢並乹並") (ℓ "並乹並丢")
                      (wnode
                        wleaf
                        (ℓ "乶亯亯") (ℓ "乶")
                        wleaf
                      )
                    )
                    (ℓ "二亘") (ℓ "亘二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京产") (ℓ "产京亨")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "乫亰乫")
                      wleaf
                    )
                  )
                  (ℓ "亘亘") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭亮") (ℓ "亮乭产")
                        wleaf
                      )
                      (ℓ "乩並") (ℓ "並世乪")
                      wleaf
                    )
                    (ℓ "么亳") (ℓ "亳么")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "乐京乐")
                        wleaf
                      )
                      (ℓ "交亨亮") (ℓ "亨亮交亨")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亰乊") (ℓ "乊京")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亮") (ℓ "亮亇")
                        wleaf
                      )
                      (ℓ "亦並丢並") (ℓ "並丢並亦")
                      (wnode
                        wleaf
                        (ℓ "主与临与") (ℓ "与临与主")
                        wleaf
                      )
                    )
                    (ℓ "亃乙亃") (ℓ "乘")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交买") (ℓ "买交")
                        wleaf
                      )
                      (ℓ "乶亪亮") (ℓ "亮乶")
                      wleaf
                    )
                  )
                  (ℓ "交乪") (ℓ "乪交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏丩亐为") (ℓ "为乏")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "乐亐乐")
                      (wnode
                        wleaf
                        (ℓ "丘丶书丷书丯丙") (ℓ "亚")
                        wleaf
                      )
                    )
                    (ℓ "乏亱") (ℓ "亱乏")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丐丩亦") (ℓ "亦丐丩")
                        wleaf
                      )
                      (ℓ "二亦亐") (ℓ "亦二")
                      wleaf
                    )
                  )
                )
                (ℓ "丯乄丰乄乇") (ℓ "乇丬么丬丯")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "争亪") (ℓ "亪争")
                        wleaf
                      )
                      (ℓ "亘么") (ℓ "么亘")
                      (wnode
                        wleaf
                        (ℓ "乪亲") (ℓ "亲乪")
                        wleaf
                      )
                    )
                    (ℓ "上丩") (ℓ "且丨且")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乒亨") (ℓ "乒亰")
                        wleaf
                      )
                      (ℓ "乊云") (ℓ "亙乊")
                      wleaf
                    )
                  )
                  (ℓ "乇乳") (ℓ "乳乢交乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯亓") (ℓ "亓丯")
                        wleaf
                      )
                      (ℓ "之亦") (ℓ "亦之")
                      wleaf
                    )
                    (ℓ "交乹") (ℓ "乹交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乗亳") (ℓ "亳乗交")
                        wleaf
                      )
                      (ℓ "亨书亨亲") (ℓ "书亲")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "乏乊") (ℓ "乊乣")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕乩") (ℓ "乩乕")
                        wleaf
                      )
                      (ℓ "串互") (ℓ "亥串")
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "书二书")
                        wleaf
                      )
                    )
                    (ℓ "乑亍") (ℓ "亙乑")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "之亓亓") (ℓ "之")
                        wleaf
                      )
                      (ℓ "丷丰亘书") (ℓ "书丷")
                      wleaf
                    )
                  )
                  (ℓ "丌二不") (ℓ "亍")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亮亲") (ℓ "亲亮")
                        wleaf
                      )
                      (ℓ "亘之亐") (ℓ "之亘")
                      (wnode
                        wleaf
                        (ℓ "亨交亳") (ℓ "亳亨")
                        wleaf
                      )
                    )
                    (ℓ "亙交交") (ℓ "亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓与") (ℓ "与乒亓")
                        wleaf
                      )
                      (ℓ "二丹") (ℓ "丹交")
                      wleaf
                    )
                  )
                )
                (ℓ "亇乊") (ℓ "乊亄")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩亭乇亭么") (ℓ "亭乇亭么乩")
                        wleaf
                      )
                      (ℓ "乕並亄並") (ℓ "並亄並乕")
                      (wnode
                        wleaf
                        (ℓ "么乹") (ℓ "乹么")
                        wleaf
                      )
                    )
                    (ℓ "二") (ℓ "乇丬么丬丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亱亱") (ℓ "亲亱亲亲亱亲")
                        wleaf
                      )
                      (ℓ "亃产") (ℓ "产亃亲")
                      wleaf
                    )
                  )
                  (ℓ "亨") (ℓ "乩乙乪乙乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交了京") (ℓ "了交")
                        wleaf
                      )
                      (ℓ "世乪亲乎亲乏") (ℓ "亲乎亲乏世乪")
                      wleaf
                    )
                    (ℓ "交") (ℓ "乜交乜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏亯") (ℓ "亯乏")
                        wleaf
                      )
                      (ℓ "乒亍亍") (ℓ "乒")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乶乊") (ℓ "乊乳")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亍产亓") (ℓ "亓亍")
                        wleaf
                      )
                      (ℓ "丐亙") (ℓ "亙丐")
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "京亮乤亮京乤")
                        wleaf
                      )
                    )
                    (ℓ "了乭了") (ℓ "乬")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丫些") (ℓ "产丫")
                        wleaf
                      )
                      (ℓ "也亙") (ℓ "亙也")
                      wleaf
                    )
                  )
                  (ℓ "丶乒") (ℓ "乒丨亐丶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩丹") (ℓ "丹乏")
                        wleaf
                      )
                      (ℓ "亲乎亲乏並亊並") (ℓ "並亊並亲乎亲乏")
                      (wnode
                        wleaf
                        (ℓ "丘临上亓") (ℓ "亓丘临上")
                        wleaf
                      )
                    )
                    (ℓ "亐丳") (ℓ "丳亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二买") (ℓ "买交二")
                        wleaf
                      )
                      (ℓ "买亏") (ℓ "亏买亦")
                      wleaf
                    )
                  )
                )
                (ℓ "丘丯乄丰乄乇丘一") (ℓ "丘乇丬么丬丯丘一")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亭乇亭么") (ℓ "亭乇亰亭么交亇乩乩亇交丢乹")
                        wleaf
                      )
                      (ℓ "亪亪") []
                      (wnode
                        wleaf
                        (ℓ "乥亓") (ℓ "亏乥")
                        wleaf
                      )
                    )
                    (ℓ "不九") (ℓ "业乞业")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乺亪") (ℓ "亪乺")
                        wleaf
                      )
                      (ℓ "交並") (ℓ "並交")
                      wleaf
                    )
                  )
                  (ℓ "亍云") (ℓ "云亍")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "並乤乤") (ℓ "並")
                        wleaf
                      )
                      (ℓ "交乖") (ℓ "乖交")
                      wleaf
                    )
                    (ℓ "交亰") (ℓ "亰交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "临与上与") (ℓ "与上与临")
                        wleaf
                      )
                      (ℓ "乶书乶") (ℓ "乥")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (ℓ "乥乼乥") (ℓ "乼乥乼")
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乐亐云") (ℓ "云亐")
                        wleaf
                      )
                      (ℓ "丞乢之乣之乎丟") (ℓ "产")
                      (wnode
                        wleaf
                        (ℓ "丘亯") (ℓ "亯丘")
                        wleaf
                      )
                    )
                    (ℓ "书乶书") (ℓ "乥")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "並乐乐") (ℓ "並")
                        wleaf
                      )
                      (ℓ "交亨") (ℓ "亨交")
                      wleaf
                    )
                  )
                  (ℓ "乇丬么丬丯") (ℓ "乇丳么丳丨")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亚") (ℓ "亚丨")
                        wleaf
                      )
                      (ℓ "亪並亄並") (ℓ "並亄並亪")
                      (wnode
                        wleaf
                        (ℓ "亘乒") (ℓ "乒二亘")
                        wleaf
                      )
                    )
                    (ℓ "乲") (ℓ "丶不丶丌丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "东") (ℓ "並乹並乹")
                        wleaf
                      )
                      (ℓ "乎亪") (ℓ "亪乎")
                      wleaf
                    )
                  )
                )
                (ℓ "丞乼") (ℓ "乼两")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乾亨亨") (ℓ "亨乾")
                        wleaf
                      )
                      (ℓ "乹並乩並") (ℓ "並乩並乹")
                      (wnode
                        wleaf
                        (ℓ "亘交亘交亘") (ℓ "亘")
                        wleaf
                      )
                    )
                    (ℓ "乬乬") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞丨买丩买乎丟") (ℓ "亓")
                        wleaf
                      )
                      (ℓ "之云云") (ℓ "之")
                      wleaf
                    )
                  )
                  (ℓ "乖亦") (ℓ "亦乖")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交乬") (ℓ "乬京")
                        wleaf
                      )
                      (ℓ "亐乶") (ℓ "乶亐")
                      (wnode
                        wleaf
                        (ℓ "产亨亨") (ℓ "产")
                        wleaf
                      )
                    )
                    (ℓ "亨亲") (ℓ "亲亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亯亯") []
                        wleaf
                      )
                      (ℓ "丹亏") (ℓ "亦丹")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乫乥") (ℓ "乥乻")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄乩") (ℓ "乩亄")
                        wleaf
                      )
                      (ℓ "争产享") (ℓ "享争")
                      (wnode
                        wleaf
                        (ℓ "亨义") (ℓ "享亨享")
                        wleaf
                      )
                    )
                    (ℓ "亐云") (ℓ "云亐乐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亩") (ℓ "亩亰京")
                        wleaf
                      )
                      (ℓ "丶丯亘丯丱亘") (ℓ "丶")
                      wleaf
                    )
                  )
                  (ℓ "亍亍") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亲亲") (ℓ "也")
                        wleaf
                      )
                      (ℓ "亘也") (ℓ "也亘")
                      (wnode
                        wleaf
                        (ℓ "乏乩") (ℓ "乩乏")
                        wleaf
                      )
                    )
                    (ℓ "丩世亏丗") (ℓ "亏二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒中上亏") (ℓ "亏丒中上")
                        wleaf
                      )
                      (ℓ "二亏") (ℓ "亏二个")
                      wleaf
                    )
                  )
                )
                (ℓ "丫乑") (ℓ "丹丫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乼") (ℓ "乼交")
                        wleaf
                      )
                      (ℓ "交") (ℓ "亨享乻享亨乻")
                      (wnode
                        wleaf
                        (ℓ "亓与临与") (ℓ "与临与亓")
                        wleaf
                      )
                    )
                    (ℓ "丨亍") (ℓ "亍丨乇二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亭乇亭么亪亭乇亰亭么亪京亲亱亲亲乎亲乏亲亨亱京亲亨") []
                        wleaf
                      )
                      (ℓ "亐个亓") (ℓ "亓亐")
                      wleaf
                    )
                  )
                  (ℓ "丌亐不") (ℓ "云")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒亄丢") (ℓ "丒亭京乐亄乐丢")
                        wleaf
                      )
                      (ℓ "丞亊丢亲乎亲乏") (ℓ "亲乎亲乏丞亊丢")
                      wleaf
                    )
                    (ℓ "交乜") (ℓ "乜交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳互些乎些乏") (ℓ "些乎些乏乳互")
                        wleaf
                      )
                      (ℓ "之亪並") (ℓ "並亪")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丫丫") []
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇亭乇亭么") (ℓ "亭乇亭么乇")
                        wleaf
                      )
                      (ℓ "亐串") (ℓ "串交")
                      (wnode
                        wleaf
                        (ℓ "乇互乇互么") (ℓ "互乇互么乇")
                        wleaf
                      )
                    )
                    (ℓ "亰") (ℓ "乹书乺书乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩亇亭乇亭么交亇交亭乇亭么") (ℓ "亭乇亭么交亇亭乇亭么交亇乩")
                        wleaf
                      )
                      (ℓ "乖丝") (ℓ "丝乖")
                      wleaf
                    )
                  )
                  (ℓ "乇丫") (ℓ "丫丯")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亍") (ℓ "亍亐交")
                        wleaf
                      )
                      (ℓ "乹並亇並") (ℓ "並亇並乹")
                      (wnode
                        wleaf
                        (ℓ "乩亳") (ℓ "亳乩乢亰")
                        wleaf
                      )
                    )
                    (ℓ "亭亭") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丐乊") (ℓ "乊世")
                        wleaf
                      )
                      (ℓ "交") (ℓ "乐交乐")
                      wleaf
                    )
                  )
                )
                (ℓ "乲丫") (ℓ "丫乵")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亄") (ℓ "丢丢丢")
                        wleaf
                      )
                      (ℓ "亊並乹並") (ℓ "並乹並亊")
                      (wnode
                        wleaf
                        (ℓ "乺亯") (ℓ "亯乺乏京")
                        wleaf
                      )
                    )
                    (ℓ "二义亍") (ℓ "亍二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亏亐") (ℓ "亏亘")
                        wleaf
                      )
                      (ℓ "亐产二") (ℓ "产亐")
                      wleaf
                    )
                  )
                  (ℓ "交") (ℓ "並交並")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亭乇亭么亲乎亲乏") (ℓ "亲乎亲乏亭乇亭么")
                        wleaf
                      )
                      (ℓ "亘丒") (ℓ "丒亘")
                      wleaf
                    )
                    (ℓ "亨义享亨") (ℓ "享")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "临与") (ℓ "与丘临上")
                        wleaf
                      )
                      (ℓ "乳乶乶") (ℓ "乳")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乙乊") (ℓ "乊乭")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丸亍") (ℓ "亍丸交")
                        wleaf
                      )
                      (ℓ "亐上") (ℓ "上亐")
                      (wnode
                        wleaf
                        (ℓ "乶亯") (ℓ "亯乶")
                        wleaf
                      )
                    )
                    (ℓ "乘乘") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交二亓") (ℓ "亓交")
                        wleaf
                      )
                      (ℓ "丰亙") (ℓ "亙丰乣亘")
                      wleaf
                    )
                  )
                  (ℓ "乏世") (ℓ "世乏")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎丨亐丨个亐") (ℓ "乎")
                        wleaf
                      )
                      (ℓ "乹並亊並") (ℓ "並亊並乹")
                      (wnode
                        wleaf
                        (ℓ "中中上") []
                        wleaf
                      )
                    )
                    (ℓ "丞亐丟") (ℓ "亓")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乊业") (ℓ "且乊")
                        wleaf
                      )
                      (ℓ "亃亦") (ℓ "亦亃亱")
                      wleaf
                    )
                  )
                )
                (ℓ "义乊") (ℓ "乊义")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乼亥") (ℓ "亩乼")
                        wleaf
                      )
                      (ℓ "亘丸亚") (ℓ "亚亘")
                      (wnode
                        wleaf
                        (ℓ "乩乺乪") (ℓ "乺")
                        wleaf
                      )
                    )
                    (ℓ "丰亍") (ℓ "亍丰么二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒二二") (ℓ "乒")
                        wleaf
                      )
                      (ℓ "交产") (ℓ "产义交")
                      wleaf
                    )
                  )
                  (ℓ "交") (ℓ "乢乒乣乒乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘亓") (ℓ "亓丘")
                        wleaf
                      )
                      (ℓ "乩亮") (ℓ "亮乩")
                      wleaf
                    )
                    (ℓ "亐产") (ℓ "产二亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭书亳") (ℓ "亳书")
                        wleaf
                      )
                      (ℓ "交亲亨乎亲亨乏並") (ℓ "亲亨乎亲亨乏並交")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "为乊") (ℓ "乊为")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎亭乇亭么") (ℓ "亭乇亭么乎")
                        wleaf
                      )
                      (ℓ "乜亓") (ℓ "亓乜产")
                      (wnode
                        wleaf
                        (ℓ "乢亯") (ℓ "亯乢")
                        wleaf
                      )
                    )
                    (ℓ "二乥") (ℓ "乥亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "亄亨亄丢亇亨亇丢亰亇亨亇丢亄亨亄丢")
                        wleaf
                      )
                      (ℓ "乖产") (ℓ "产乖")
                      wleaf
                    )
                  )
                  (ℓ "乊亦") (ℓ "亥乊")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒亄丢") (ℓ "丒亩亨义亄义丢")
                        wleaf
                      )
                      (ℓ "亨乽") (ℓ "乽交亨")
                      (wnode
                        wleaf
                        (ℓ "两乇亃么亃乩严") (ℓ "享")
                        wleaf
                      )
                    )
                    (ℓ "丒二专") (ℓ "于")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "世") (ℓ "並乩並乩")
                        wleaf
                      )
                      (ℓ "亐云") (ℓ "云乐亐")
                      wleaf
                    )
                  )
                )
                (ℓ "乘乥") (ℓ "乥乘")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "之京京") (ℓ "之")
                        wleaf
                      )
                      (ℓ "世云") (ℓ "云世")
                      (wnode
                        wleaf
                        (ℓ "乶享") (ℓ "享乶亯")
                        wleaf
                      )
                    )
                    (ℓ "亰") (ℓ "乢争乣争乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亐亏") (ℓ "亏交")
                        wleaf
                      )
                      (ℓ "亰乫亲") (ℓ "亲亰")
                      wleaf
                    )
                  )
                  (ℓ "乖乣") (ℓ "乣乖")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰产") (ℓ "产丰")
                        wleaf
                      )
                      (ℓ "世乪並") (ℓ "並乩")
                      (wnode
                        wleaf
                        (ℓ "乏亏") (ℓ "亏乏")
                        wleaf
                      )
                    )
                    (ℓ "亘") (ℓ "乢丳乣丳丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乐亯") (ℓ "亯京")
                        wleaf
                      )
                      (ℓ "么乏交乏乐交") (ℓ "么")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丷丫") (ℓ "丫乏")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亄交亭乇亭么") (ℓ "亭乇亭么亄")
                        wleaf
                      )
                      (ℓ "亇並丢並") (ℓ "並丢並亇")
                      (wnode
                        wleaf
                        (ℓ "主与主与") (ℓ "与主与主")
                        wleaf
                      )
                    )
                    (ℓ "二交") (ℓ "交二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为二二") (ℓ "为")
                        wleaf
                      )
                      (ℓ "乶亮") (ℓ "亮乶亪")
                      wleaf
                    )
                  )
                  (ℓ "京") (ℓ "业京业")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏丩亐丩个亐") (ℓ "乏")
                        wleaf
                      )
                      (ℓ "亐乐云") (ℓ "云亐")
                      (wnode
                        wleaf
                        (ℓ "主亘主上") (ℓ "些")
                        wleaf
                      )
                    )
                    (ℓ "交亱") (ℓ "亱交京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨与上与") (ℓ "与上与丨")
                        wleaf
                      )
                      (ℓ "亃亱") (ℓ "亱亃")
                      wleaf
                    )
                  )
                )
                (ℓ "乎丫") (ℓ "丫丶")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "並义义") (ℓ "並")
                        wleaf
                      )
                      (ℓ "交京") (ℓ "京交")
                      (wnode
                        wleaf
                        (ℓ "亏亓亓") (ℓ "亏")
                        wleaf
                      )
                    )
                    (ℓ "久") (ℓ "丩不丩丌丩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏亓") (ℓ "亓亏")
                        wleaf
                      )
                      (ℓ "乶云") (ℓ "云乶")
                      wleaf
                    )
                  )
                  (ℓ "交云") (ℓ "云交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亓") (ℓ "亓交二")
                        wleaf
                      )
                      (ℓ "之乒亦") (ℓ "亦乒")
                      wleaf
                    )
                    (ℓ "交丶") (ℓ "丶交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "么些乎些乏") (ℓ "些乎些乏么")
                        wleaf
                      )
                      (ℓ "乜书亙") (ℓ "亙书")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丌丫") (ℓ "丫丒")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢亲乎亲乏") (ℓ "亲乎亲乏丢")
                        wleaf
                      )
                      (ℓ "丳亓亓") (ℓ "丳")
                      (wnode
                        wleaf
                        (ℓ "京书亨") (ℓ "书京")
                        wleaf
                      )
                    )
                    (ℓ "亨亰亨亰亨") (ℓ "亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亰亰") (ℓ "也")
                        wleaf
                      )
                      (ℓ "书亮") (ℓ "亮书")
                      wleaf
                    )
                  )
                  (ℓ "主乊") (ℓ "乊主")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "争亭乇亭么") (ℓ "亭乇亰亭么交亊乹乹亊交丢乩")
                        wleaf
                      )
                      (ℓ "亮並亇並") (ℓ "並亇並亮")
                      (wnode
                        wleaf
                        (ℓ "与乻乻") (ℓ "与")
                        wleaf
                      )
                    )
                    (ℓ "乣亭") (ℓ "亭乣")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亓与") (ℓ "与亓")
                        wleaf
                      )
                      (ℓ "为亏亏") (ℓ "为")
                      wleaf
                    )
                  )
                )
                (ℓ "亇乥") (ℓ "乥亊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰") (ℓ "亭乇亭么亭乇亭么")
                        wleaf
                      )
                      (ℓ "不亐") (ℓ "云不")
                      (wnode
                        wleaf
                        (ℓ "乙亯") (ℓ "亯乙")
                        wleaf
                      )
                    )
                    (ℓ "二不") (ℓ "不亍")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亓个") (ℓ "亓亐")
                        wleaf
                      )
                      (ℓ "乙产") (ℓ "产乙")
                      wleaf
                    )
                  )
                  (ℓ "交乇交亨亲乎") (ℓ "亲乇乎亨")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭交交") (ℓ "乭")
                        wleaf
                      )
                      (ℓ "丞亊丢亱") (ℓ "亱丞亊丢")
                      wleaf
                    )
                    (ℓ "交义产交") (ℓ "产")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乫亯") (ℓ "亯乫交")
                        wleaf
                      )
                      (ℓ "丶么") (ℓ "么丶")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "了乥") (ℓ "乥争")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨乎亐乎乐亐") (ℓ "丨")
                        wleaf
                      )
                      (ℓ "亦並乕並") (ℓ "並乕並亦")
                      (wnode
                        wleaf
                        (ℓ "京乥") (ℓ "乥亨")
                        wleaf
                      )
                    )
                    (ℓ "交") (ℓ "乇乶么乶乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亚亦") (ℓ "亦亚")
                        wleaf
                      )
                      (ℓ "亘乤") (ℓ "亙亘亙")
                      wleaf
                    )
                  )
                  (ℓ "亐亦") (ℓ "亦亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亥个亥交个丹") (ℓ "丹二于乐于二乐")
                        wleaf
                      )
                      (ℓ "京") (ℓ "乹乙乺乙乎")
                      (wnode
                        wleaf
                        (ℓ "么亓") (ℓ "亓么")
                        wleaf
                      )
                    )
                    (ℓ "亲亲") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亳交") (ℓ "亳京")
                        wleaf
                      )
                      (ℓ "京亦") (ℓ "亦京")
                      wleaf
                    )
                  )
                )
                (ℓ "亨乊") (ℓ "乊亨")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交乩乩") (ℓ "乩乩交")
                        wleaf
                      )
                      (ℓ "乖丗") (ℓ "丗乖")
                      (wnode
                        wleaf
                        (ℓ "乺乶") (ℓ "乶乺")
                        wleaf
                      )
                    )
                    (ℓ "下丯") (ℓ "业丰业")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亏亏") (ℓ "乒")
                        wleaf
                      )
                      (ℓ "交亪京") (ℓ "亪京交京")
                      wleaf
                    )
                  )
                  (ℓ "乶亍") (ℓ "亍乶云")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰並乤") (ℓ "並亰")
                        wleaf
                      )
                      (ℓ "丞亪") (ℓ "亪丞")
                      wleaf
                    )
                    (ℓ "交") (ℓ "义交义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些乎些乏与临与") (ℓ "与临与些乎些乏")
                        wleaf
                      )
                      (ℓ "书云") (ℓ "云书亍")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "乊乊") []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乒亨亮") (ℓ "乒亮")
                        wleaf
                      )
                      (ℓ "交亥乗亥交乗") (ℓ "亰")
                      (wnode
                        wleaf
                        (ℓ "乎互乇互么") (ℓ "互乇互么乎")
                        wleaf
                      )
                    )
                    (ℓ "亨京亨京亨") (ℓ "亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交丢") (ℓ "丢交")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "丱亘丱")
                      wleaf
                    )
                  )
                  (ℓ "丒乇丬么丬丯丒一") (ℓ "丒乇丬么丬丯丒丂")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亚亐") (ℓ "亚交")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "争亨争")
                      (wnode
                        wleaf
                        (ℓ "乑亳") (ℓ "享乑")
                        wleaf
                      )
                    )
                    (ℓ "不乱") (ℓ "丠乲丠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交乇交亨亲乎") (ℓ "亲乎乇亨")
                        wleaf
                      )
                      (ℓ "乏亪") (ℓ "亪乏")
                      wleaf
                    )
                  )
                )
                (ℓ "亃乥") (ℓ "乥亃")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乿亨亨") (ℓ "亨乿")
                        wleaf
                      )
                      (ℓ "交世") (ℓ "世交")
                      (wnode
                        wleaf
                        (ℓ "乏亚") (ℓ "亚乏")
                        wleaf
                      )
                    )
                    (ℓ "交") (ℓ "乎也乏也乢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亦京") (ℓ "亦亨")
                        wleaf
                      )
                      (ℓ "亐乊") (ℓ "乊亘")
                      wleaf
                    )
                  )
                  (ℓ "亪亪亮") (ℓ "亮")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨京") (ℓ "京亨")
                        wleaf
                      )
                      (ℓ "丢並") (ℓ "並一丣")
                      (wnode
                        wleaf
                        (ℓ "交亐亏亐") (ℓ "亏亐交")
                        wleaf
                      )
                    )
                    (ℓ "严两") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "也亘也")
                        wleaf
                      )
                      (ℓ "乎亦") (ℓ "亦乎")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乊亲") (ℓ "亮乊")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹亲乎亲乏") (ℓ "亲乎亲乏乹")
                        wleaf
                      )
                      (ℓ "乕並丢並") (ℓ "並丢並乕")
                      (wnode
                        wleaf
                        (ℓ "丞主上与") (ℓ "与主")
                        wleaf
                      )
                    )
                    (ℓ "二乢") (ℓ "乢二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乜交交") (ℓ "乜")
                        wleaf
                      )
                      (ℓ "书书") []
                      wleaf
                    )
                  )
                  (ℓ "京") (ℓ "乹乒乺乒乕")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇些") (ℓ "些乇")
                        wleaf
                      )
                      (ℓ "京也") (ℓ "也亰京")
                      (wnode
                        wleaf
                        (ℓ "亚与主与") (ℓ "与主与亚")
                        wleaf
                      )
                    )
                    (ℓ "二云") (ℓ "云二交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "与上") (ℓ "一下与")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "乻亰乻")
                      wleaf
                    )
                  )
                )
                (ℓ "乊亍") (ℓ "亍乊")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "交亥个亥交个")
                        wleaf
                      )
                      (ℓ "丬亘亘") (ℓ "丬")
                      (wnode
                        wleaf
                        (ℓ "亰乫书") (ℓ "书亰")
                        wleaf
                      )
                    )
                    (ℓ "个亍") (ℓ "亍个义")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亨产") (ℓ "产亰")
                        wleaf
                      )
                      (ℓ "产二二") (ℓ "产")
                      wleaf
                    )
                  )
                  (ℓ "亐亐") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乗") (ℓ "亮京亮")
                        wleaf
                      )
                      (ℓ "丘亇丢亭乇亭么") (ℓ "亭乇亭么丘亇丢")
                      wleaf
                    )
                    (ℓ "亨亩乐亩亨乐") (ℓ "亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "互与") (ℓ "与乳互")
                        wleaf
                      )
                      (ℓ "丰並") (ℓ "並丰")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "书乊") (ℓ "乊乒")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹丢") (ℓ "丢乹")
                        wleaf
                      )
                      (ℓ "乜产") (ℓ "产乜")
                      (wnode
                        wleaf
                        (ℓ "亳一下") (ℓ "一下亳")
                        wleaf
                      )
                    )
                    (ℓ "乒乳乒") (ℓ "乑")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亨亄丢") (ℓ "亩")
                        wleaf
                      )
                      (ℓ "京乢") (ℓ "乢京")
                      wleaf
                    )
                  )
                  (ℓ "乊产") (ℓ "产乊")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二乶亐") (ℓ "乶二")
                        wleaf
                      )
                      (ℓ "丘交") (ℓ "亦丘")
                      (wnode
                        wleaf
                        (ℓ "乪亳") (ℓ "亳乪乣亰")
                        wleaf
                      )
                    )
                    (ℓ "交乭") (ℓ "乭交")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亦与上与") (ℓ "与上与亦")
                        wleaf
                      )
                      (ℓ "亰亦") (ℓ "亦亰京")
                      wleaf
                    )
                  )
                )
                (ℓ "义丹") (ℓ "丹义")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩亇乩亇乩亇") (ℓ "丢丢丢")
                        wleaf
                      )
                      (ℓ "亭乇亭么並乹並") (ℓ "並乹並亭乇亭么")
                      (wnode
                        wleaf
                        (ℓ "乐京亯") (ℓ "亯京")
                        wleaf
                      )
                    )
                    (ℓ "亐丰") (ℓ "丰亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏亐亐") (ℓ "亏")
                        wleaf
                      )
                      (ℓ "交乘") (ℓ "乘亰")
                      wleaf
                    )
                  )
                  (ℓ "乇亲") (ℓ "亲乇")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘些") (ℓ "些亘丱")
                        wleaf
                      )
                      (ℓ "丘亇丢亮") (ℓ "亮丘亇丢")
                      wleaf
                    )
                    (ℓ "享享") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亳") (ℓ "亳亰乤")
                        wleaf
                      )
                      (ℓ "乇亮") (ℓ "亮乇")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乊亱") (ℓ "亭乊")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丶丷") []
                        wleaf
                      )
                      (ℓ "乹並乕並") (ℓ "並乕並乹")
                      (wnode
                        wleaf
                        (ℓ "书享享") (ℓ "书")
                        wleaf
                      )
                    )
                    (ℓ "京") (ℓ "乕乽乖乽乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交京") (ℓ "亱交亱")
                        wleaf
                      )
                      (ℓ "丯亙") (ℓ "亙丯乢亘")
                      wleaf
                    )
                  )
                  (ℓ "二亍丸亍二丸") (ℓ "交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亲") (ℓ "亲亨京")
                        wleaf
                      )
                      (ℓ "交亃亰") (ℓ "亃交")
                      (wnode
                        wleaf
                        (ℓ "二亓交二") (ℓ "交二亓")
                        wleaf
                      )
                    )
                    (ℓ "乪东亲丝") (ℓ "亲亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨丫") (ℓ "丫丨")
                        wleaf
                      )
                      (ℓ "二个") (ℓ "亏二亏")
                      wleaf
                    )
                  )
                )
                (ℓ "丫丂") (ℓ "丂丫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄乕乕亄丢") (ℓ "亃")
                        wleaf
                      )
                      (ℓ "丷世亚丗") (ℓ "亚亘")
                      (wnode
                        wleaf
                        (ℓ "乹乩亰乩乫亰") (ℓ "乹")
                        wleaf
                      )
                    )
                    (ℓ "乜亍") (ℓ "亍乜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乳亰") (ℓ "乳亨")
                        wleaf
                      )
                      (ℓ "么产") (ℓ "产么")
                      wleaf
                    )
                  )
                  (ℓ "乢云") (ℓ "云乢")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "丶乜丷乜乢")
                        wleaf
                      )
                      (ℓ "交亪") (ℓ "亪京交")
                      wleaf
                    )
                    (ℓ "二") (ℓ "亐二亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎与") (ℓ "与乎")
                        wleaf
                      )
                      (ℓ "专亙") (ℓ "亙专")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "乖乊") (ℓ "乊乪")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亭亭乇亭么") (ℓ "亭乇亭么乳亭")
                        wleaf
                      )
                      (ℓ "乜产产") (ℓ "乜")
                      (wnode
                        wleaf
                        (ℓ "乳互互乇互么") (ℓ "互乇互么乳互")
                        wleaf
                      )
                    )
                    (ℓ "二") (ℓ "丨也丩也丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亇交亨交亇交丢亰亰亰亭乇亰亰亭么交交亇交交亨交交亇") (ℓ "亇交亨交亇交丢亰亰亰亭乇亰亰亭么交交亇交交亨交交亇交")
                        wleaf
                      )
                      (ℓ "丞亘丟") (ℓ "些")
                      wleaf
                    )
                  )
                  (ℓ "乼亮") (ℓ "亯乼")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐也亘") (ℓ "也亐")
                        wleaf
                      )
                      (ℓ "亭乇亭么並亄並") (ℓ "並亄並亭乇亭么")
                      (wnode
                        wleaf
                        (ℓ "乳亳亳") (ℓ "乳")
                        wleaf
                      )
                    )
                    (ℓ "乺丐亭丑") (ℓ "亭京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亦") (ℓ "亦丩")
                        wleaf
                      )
                      (ℓ "乎云") (ℓ "云乎")
                      wleaf
                    )
                  )
                )
                (ℓ "买丫") (ℓ "丫乳")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢丢丢丢") []
                        wleaf
                      )
                      (ℓ "乩並乹並") (ℓ "並乹並乩")
                      (wnode
                        wleaf
                        (ℓ "乥亭") (ℓ "亩乥")
                        wleaf
                      )
                    )
                    (ℓ "亨") (ℓ "乇亃么亃乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些产") (ℓ "产些")
                        wleaf
                      )
                      (ℓ "亰亲") (ℓ "亲亰乫")
                      wleaf
                    )
                  )
                  (ℓ "个亙") (ℓ "亙个交")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭产产") (ℓ "乭")
                        wleaf
                      )
                      (ℓ "东乺亦") (ℓ "亦东乺")
                      wleaf
                    )
                    (ℓ "交") (ℓ "亨交亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乐亯京") (ℓ "亯")
                        wleaf
                      )
                      (ℓ "亨亮") (ℓ "亮亨")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乎乊") (ℓ "乊乢")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乤亏") (ℓ "亏乤亐")
                        wleaf
                      )
                      (ℓ "亲乎亲乏並丢並") (ℓ "並丢並亲乎亲乏")
                      (wnode
                        wleaf
                        (ℓ "主与中与") (ℓ "与中与主")
                        wleaf
                      )
                    )
                    (ℓ "亰亃") (ℓ "亃亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丳亐亐") (ℓ "丳")
                        wleaf
                      )
                      (ℓ "亐云丱云亐丱乥") (ℓ "乥二亍丸亍二丸")
                      wleaf
                    )
                  )
                  (ℓ "丘交丙") (ℓ "亦")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨乏丩") (ℓ "乏")
                        wleaf
                      )
                      (ℓ "亭乇亭么並亇並") (ℓ "並亇並亭乇亭么")
                      (wnode
                        wleaf
                        (ℓ "丘丶乜丷乜乢丙") (ℓ "亚")
                        wleaf
                      )
                    )
                    (ℓ "云交交") (ℓ "云")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨与中与") (ℓ "与中与丨")
                        wleaf
                      )
                      (ℓ "亦亱") (ℓ "亱亦")
                      wleaf
                    )
                  )
                )
                (ℓ "丌丯乄丰乄乇丌一") (ℓ "丌乇丬么丬丯丌一")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亦亐") (ℓ "亦亘")
                        wleaf
                      )
                      (ℓ "亨亪") (ℓ "亪亨乗")
                      (wnode
                        wleaf
                        (ℓ "书亓") (ℓ "亓书")
                        wleaf
                      )
                    )
                    (ℓ "丌乆") (ℓ "且久且")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亏") (ℓ "亏乳亚")
                        wleaf
                      )
                      (ℓ "乪产") (ℓ "产乪")
                      wleaf
                    )
                  )
                  (ℓ "乢亭") (ℓ "亭乢")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亇") (ℓ "乤亇乤亰")
                        wleaf
                      )
                      (ℓ "京乗亮京") (ℓ "亮")
                      wleaf
                    )
                    (ℓ "交") (ℓ "京亯乫亯京乫")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二些乎二些乏与交") (ℓ "交二些乎二些乏与")
                        wleaf
                      )
                      (ℓ "乏亲乎亲乏") (ℓ "亲乎亲乏乏")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亘丫") (ℓ "丫交")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇乕") (ℓ "乕亇")
                        wleaf
                      )
                      (ℓ "乖亲") (ℓ "亲乖")
                      (wnode
                        wleaf
                        (ℓ "二乶") (ℓ "乶亐二")
                        wleaf
                      )
                    )
                    (ℓ "乑亚") (ℓ "亏乑")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒乩之乪之乕专") (ℓ "亩")
                        wleaf
                      )
                      (ℓ "丯丷丰") (ℓ "丷")
                      wleaf
                    )
                  )
                  (ℓ "么上亍下") (ℓ "亍二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞乕乳乖乳乹丟") (ℓ "亮")
                        wleaf
                      )
                      (ℓ "亘乎") (ℓ "乎亘")
                      (wnode
                        wleaf
                        (ℓ "之亏些乎些乏") (ℓ "些乎些乏之亏")
                        wleaf
                      )
                    )
                    (ℓ "亰么") (ℓ "么亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乺与") (ℓ "与乺")
                        wleaf
                      )
                      (ℓ "交丹") (ℓ "丹二")
                      wleaf
                    )
                  )
                )
                (ℓ "乷乊") (ℓ "乊乴")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹亭乇亭么") (ℓ "亭乇亭么乹")
                        wleaf
                      )
                      (ℓ "乹並亄並") (ℓ "並亄並乹")
                      (wnode
                        wleaf
                        (ℓ "么乺") (ℓ "乺么")
                        wleaf
                      )
                    )
                    (ℓ "上乇二乇义二") (ℓ "上")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘乹书乺书乩丙") (ℓ "亱")
                        wleaf
                      )
                      (ℓ "乭产") (ℓ "产乭")
                      wleaf
                    )
                  )
                  (ℓ "乎亙") (ℓ "亙乎")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交些二") (ℓ "些交")
                        wleaf
                      )
                      (ℓ "丒亄丢亲乎亲乏") (ℓ "亲乎亲乏丒亄丢")
                      wleaf
                    )
                    (ℓ "乎享") (ℓ "享乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎亯") (ℓ "亯乎")
                        wleaf
                      )
                      (ℓ "乑亏") (ℓ "亚乑")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乗乥") (ℓ "乥乗")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐丠个") (ℓ "丠亐")
                        wleaf
                      )
                      (ℓ "亭乇亭么並乕並") (ℓ "並乕並亭乇亭么")
                      (wnode
                        wleaf
                        (ℓ "亨亯交") (ℓ "亯亨")
                        wleaf
                      )
                    )
                    (ℓ "京了") (ℓ "了京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亪") (ℓ "亪京亰")
                        wleaf
                      )
                      (ℓ "之亙") (ℓ "亙之云")
                      wleaf
                    )
                  )
                  (ℓ "丞乹乒乺乒乕丟") (ℓ "亮")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了产") (ℓ "产了亮")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "乇了么了乕")
                      (wnode
                        wleaf
                        (ℓ "之亳") (ℓ "亳之亯")
                        wleaf
                      )
                    )
                    (ℓ "丌乇丬么丬丯不") (ℓ "亍")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二交二交二") (ℓ "二")
                        wleaf
                      )
                      (ℓ "乒亏") (ℓ "亏乒")
                      wleaf
                    )
                  )
                )
                (ℓ "乥亦") (ℓ "产乥")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "交亚") (ℓ "亚交亐")
                        wleaf
                      )
                      (ℓ "亨乣") (ℓ "乣亨")
                      (wnode
                        wleaf
                        (ℓ "乒亳") (ℓ "亳乒享")
                        wleaf
                      )
                    )
                    (ℓ "二丸") (ℓ "丸二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨京亲") (ℓ "亲京")
                        wleaf
                      )
                      (ℓ "书亲並") (ℓ "並亲")
                      wleaf
                    )
                  )
                  (ℓ "京") (ℓ "乶京乶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐些二") (ℓ "些亐")
                        wleaf
                      )
                      (ℓ "亨乗亪") (ℓ "亪亨")
                      wleaf
                    )
                    (ℓ "亐交亐交亐") (ℓ "亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些乎些乏与上与") (ℓ "与上与些乎些乏")
                        wleaf
                      )
                      (ℓ "京亨京亨京") (ℓ "京")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

windowsP : WTree
windowsP =
  (wnode
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五乭") (ℓ "乭二五")
                        wleaf
                      )
                      (ℓ "亜丫") (ℓ "丫亨")
                      wleaf
                    )
                    (ℓ "亁") (ℓ "举不举丌举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓乹亓乺与上与") (ℓ "与上与亓乹亓乺")
                        wleaf
                      )
                      (ℓ "亜") (ℓ "亨亩个亩亨个")
                      wleaf
                    )
                  )
                  (ℓ "亠乳") (ℓ "乳亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亞") (ℓ "亞买亱")
                        wleaf
                      )
                      (ℓ "么上举") (ℓ "上举么")
                      wleaf
                    )
                    (ℓ "五亨五亨五") (ℓ "五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄亯") (ℓ "亯乄")
                        wleaf
                      )
                      (ℓ "京亓") (ℓ "亓京五")
                      wleaf
                    )
                  )
                )
                (ℓ "五乺") (ℓ "乺五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨乁") (ℓ "乁二亨")
                        wleaf
                      )
                      (ℓ "亘亠") (ℓ "亠亘")
                      wleaf
                    )
                    (ℓ "举亣") (ℓ "亣举丷亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯亗") (ℓ "亗丯")
                        wleaf
                      )
                      (ℓ "亠亭") (ℓ "亭亠")
                      wleaf
                    )
                  )
                  (ℓ "也亝") (ℓ "亝也")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亱亠亠") (ℓ "亱")
                        wleaf
                      )
                      (ℓ "丰乖") (ℓ "乖丰")
                      wleaf
                    )
                    (ℓ "丽並乩並") (ℓ "並乩並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰亟") (ℓ "亟丰")
                        wleaf
                      )
                      (ℓ "乼亖") (ℓ "互乼")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "並丨亐五") (ℓ "並乒乒丨亐五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亢") (ℓ "亢了")
                        wleaf
                      )
                      (ℓ "亘乹") (ℓ "乹亘")
                      wleaf
                    )
                    (ℓ "亃亡亡") (ℓ "亃")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为亟") (ℓ "亟为")
                        wleaf
                      )
                      (ℓ "二之亪") (ℓ "之亪个五二")
                      wleaf
                    )
                  )
                  (ℓ "五乗") (ℓ "井五井")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乖亞") (ℓ "亞乖")
                        wleaf
                      )
                      (ℓ "亨丬") (ℓ "丬亜亨")
                      wleaf
                    )
                    (ℓ "亁並丽並") (ℓ "並丽並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五享") (ℓ "享五二")
                        wleaf
                      )
                      (ℓ "亜亁") (ℓ "丱亁丱亜")
                      wleaf
                    )
                  )
                )
                (ℓ "乹云") (ℓ "云乹")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜") (ℓ "亁五亁丢亄五亄丢亨亄五亄丢亁五亁丢")
                        wleaf
                      )
                      (ℓ "丶世乪") (ℓ "世乪丶")
                      wleaf
                    )
                    (ℓ "亢亢") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丷亯") (ℓ "亯丷")
                        wleaf
                      )
                      (ℓ "丶乩") (ℓ "乩丶")
                      wleaf
                    )
                  )
                  (ℓ "亠下") (ℓ "下亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乖亍") (ℓ "亍乖")
                        wleaf
                      )
                      (ℓ "亠乙亐") (ℓ "乙亠")
                      wleaf
                    )
                    (ℓ "亮丶亮丷並亁並") (ℓ "並亁並亮丶亮丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "京亮丸亮京丸")
                        wleaf
                      )
                      (ℓ "亜五亜五亜") (ℓ "亜")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "举世亞丗") (ℓ "亞亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五京亢") (ℓ "亢京")
                        wleaf
                      )
                      (ℓ "亘乼") (ℓ "乼亜")
                      wleaf
                    )
                    (ℓ "了亡亡") (ℓ "了")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽与上与") (ℓ "与上与丽")
                        wleaf
                      )
                      (ℓ "云井亮") (ℓ "亮云")
                      wleaf
                    )
                  )
                  (ℓ "亃亜亜") (ℓ "亃")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁亏") (ℓ "亏乁")
                        wleaf
                      )
                      (ℓ "五") (ℓ "之五之")
                      wleaf
                    )
                    (ℓ "乼亓") (ℓ "亗乼")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亗亓亯") (ℓ "亯亓")
                        wleaf
                      )
                      (ℓ "亜乽亘") (ℓ "乽亜")
                      wleaf
                    )
                  )
                )
                (ℓ "乪上亝下") (ℓ "亝亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乀亲") (ℓ "些乀")
                        wleaf
                      )
                      (ℓ "亝亡") (ℓ "亡亝")
                      wleaf
                    )
                    (ℓ "亗享") (ℓ "享亗")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亟与临与") (ℓ "与临与亟")
                        wleaf
                      )
                      (ℓ "丽丢") (ℓ "丢丽")
                      wleaf
                    )
                  )
                  (ℓ "乑亡") (ℓ "井乑")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亠五亠五") (ℓ "五")
                        wleaf
                      )
                      (ℓ "乥亞") (ℓ "亢乥")
                      wleaf
                    )
                    (ℓ "亁並乹並") (ℓ "並乹並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亠互亠") (ℓ "乳互")
                        wleaf
                      )
                      (ℓ "亃亍") (ℓ "亍亃亝")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亘举") (ℓ "举亘")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亢亜") (ℓ "亢亰")
                        wleaf
                      )
                      (ℓ "亰亞") (ℓ "亞亰亠")
                      wleaf
                    )
                    (ℓ "两五严") (ℓ "亗")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亟亘") (ℓ "亟亰")
                        wleaf
                      )
                      (ℓ "亜井") (ℓ "井亜亨")
                      wleaf
                    )
                  )
                  (ℓ "亘乬") (ℓ "乬亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹亚") (ℓ "亚乹")
                        wleaf
                      )
                      (ℓ "五亢") (ℓ "亢五")
                      wleaf
                    )
                    (ℓ "举亝") (ℓ "亝举乪亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓乹亓乺与主与") (ℓ "与主与亓乹亓乺")
                        wleaf
                      )
                      (ℓ "亚亞") (ℓ "亞亚")
                      wleaf
                    )
                  )
                )
                (ℓ "亘亚乫亚亘乫") (ℓ "亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜") (ℓ "亠亜亠")
                        wleaf
                      )
                      (ℓ "上举亲") (ℓ "亲上举")
                      wleaf
                    )
                    (ℓ "乎亗") (ℓ "亗乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亣") (ℓ "亣亠丸")
                        wleaf
                      )
                      (ℓ "亇丷") (ℓ "丷亇")
                      wleaf
                    )
                  )
                  (ℓ "乻亡") (ℓ "亡乻")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌") (ℓ "並亁並亁")
                        wleaf
                      )
                      (ℓ "丙亡") (ℓ "亡丙")
                      wleaf
                    )
                    (ℓ "亁並亄並") (ℓ "並亄並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞主上亓乹亓乺") (ℓ "亓乹亓乺丞主上")
                        wleaf
                      )
                      (ℓ "些亲") (ℓ "亲些")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "亠亠") []
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亮") (ℓ "亮亠五")
                        wleaf
                      )
                      (ℓ "争亝") (ℓ "亝争")
                      wleaf
                    )
                    (ℓ "乭亙") (ℓ "亙乭")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乒亓亓乹亓乺") (ℓ "亓乹亓乺乒亓")
                        wleaf
                      )
                      (ℓ "为亜亜") (ℓ "为")
                      wleaf
                    )
                  )
                  (ℓ "亜亜") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亢") (ℓ "亢亐五")
                        wleaf
                      )
                      (ℓ "丢云") (ℓ "云丢")
                      wleaf
                    )
                    (ℓ "五享") (ℓ "享二五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨享") (ℓ "享丨")
                        wleaf
                      )
                      (ℓ "亁亁") (ℓ "丢丢丢")
                      wleaf
                    )
                  )
                )
                (ℓ "五亝亨") (ℓ "亝五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亀京") (ℓ "亀亐")
                        wleaf
                      )
                      (ℓ "乬井") (ℓ "亍乬")
                      wleaf
                    )
                    (ℓ "亠丶") (ℓ "丶亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五与乗") (ℓ "与五")
                        wleaf
                      )
                      (ℓ "亜亨井") (ℓ "井亜")
                      wleaf
                    )
                  )
                  (ℓ "亘亡") (ℓ "亡亘亰")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亏") (ℓ "亏亨五")
                        wleaf
                      )
                      (ℓ "丬亞亞") (ℓ "丬")
                      wleaf
                    )
                    (ℓ "世丽亜丽丿亜") (ℓ "世")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亘亣") (ℓ "亣亜")
                        wleaf
                      )
                      (ℓ "亘亝") (ℓ "亝亘亰")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜丨") (ℓ "丨亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亢") (ℓ "亢亰亜")
                        wleaf
                      )
                      (ℓ "亜乊") (ℓ "乊五")
                      wleaf
                    )
                    (ℓ "亠亲") (ℓ "亲亜亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亳亳") (ℓ "买")
                        wleaf
                      )
                      (ℓ "五乽亐") (ℓ "乽五")
                      wleaf
                    )
                  )
                  (ℓ "二五") (ℓ "五二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄亨亨") (ℓ "乄")
                        wleaf
                      )
                      (ℓ "亨丰") (ℓ "丰亨")
                      wleaf
                    )
                    (ℓ "乖井") (ℓ "井乖")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰亣") (ℓ "亣丰")
                        wleaf
                      )
                      (ℓ "丒亄丢") (ℓ "丒亖五个亄个丢")
                      wleaf
                    )
                  )
                )
                (ℓ "亠京") (ℓ "京亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄五亄丢") (ℓ "亖")
                        wleaf
                      )
                      (ℓ "丷丘亇丢") (ℓ "丘亇丢丷")
                      wleaf
                    )
                    (ℓ "二亗") (ℓ "亗二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五一下") (ℓ "一下五")
                        wleaf
                      )
                      (ℓ "亁乎") (ℓ "乎亁")
                      wleaf
                    )
                  )
                  (ℓ "亠") (ℓ "乹为乺为丽")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亍") (ℓ "亍亨五")
                        wleaf
                      )
                      (ℓ "亨亝") (ℓ "亝亨")
                      wleaf
                    )
                    (ℓ "丽亝") (ℓ "亝丽乩亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞亟") (ℓ "亟丞")
                        wleaf
                      )
                      (ℓ "为亝") (ℓ "亝亲为")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜丱") (ℓ "丱亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "亝丨亝丩亝丨亝丩")
                        wleaf
                      )
                      (ℓ "乩丽亜丽丿亜") (ℓ "乩")
                      wleaf
                    )
                    (ℓ "亰丯") (ℓ "丯亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨与丽与") (ℓ "与丽与丨")
                        wleaf
                      )
                      (ℓ "乳亠亭亠") (ℓ "乳亭")
                      wleaf
                    )
                  )
                  (ℓ "亠乘") (ℓ "乘亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亱") (ℓ "亱买")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "乄亨乄")
                      wleaf
                    )
                    (ℓ "五並丢並") (ℓ "並丢並五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹与临与") (ℓ "与临与乹")
                        wleaf
                      )
                      (ℓ "亨丨") (ℓ "丨亨")
                      wleaf
                    )
                  )
                )
                (ℓ "亜么") (ℓ "么亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢些") (ℓ "些丢")
                        wleaf
                      )
                      (ℓ "亮丶亮丷一丣") (ℓ "一丣亮丶亮丷")
                      wleaf
                    )
                    (ℓ "丞亠丟") (ℓ "亢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亳") (ℓ "亳亘")
                        wleaf
                      )
                      (ℓ "亊丽") (ℓ "丽亊")
                      wleaf
                    )
                  )
                  (ℓ "五丰") (ℓ "丰五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌乕乁乖乁丨不") (ℓ "井")
                        wleaf
                      )
                      (ℓ "亜") (ℓ "亃亜亃")
                      wleaf
                    )
                    (ℓ "乕並亁並") (ℓ "並亁並乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亗") (ℓ "亗丩")
                        wleaf
                      )
                      (ℓ "书亡") (ℓ "亡书亝")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五个") (ℓ "个五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "乁二乁")
                        wleaf
                      )
                      (ℓ "亐亃") (ℓ "亃亠亐")
                      wleaf
                    )
                    (ℓ "丯亳") (ℓ "亳丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亟二") (ℓ "亟五")
                        wleaf
                      )
                      (ℓ "乺亙") (ℓ "亙乺")
                      wleaf
                    )
                  )
                  (ℓ "亠亝") (ℓ "亝亠亰")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亠亠") (ℓ "丬")
                        wleaf
                      )
                      (ℓ "丫亢") (ℓ "亮丫")
                      wleaf
                    )
                    (ℓ "么並丽並") (ℓ "並丽並么")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐") (ℓ "亣亐亣")
                        wleaf
                      )
                      (ℓ "亐亄亐亐") (ℓ "亐亄")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乻亡亠") (ℓ "亡")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "丨亀丩亀乕")
                        wleaf
                      )
                      (ℓ "乎丌亁丢") (ℓ "丌亁丢乎")
                      wleaf
                    )
                    (ℓ "亠") (ℓ "丸亠丸")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠丸亣") (ℓ "亣亠")
                        wleaf
                      )
                      (ℓ "亝丠") (ℓ "丠亝")
                      wleaf
                    )
                  )
                  (ℓ "二丿") (ℓ "丿二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩亇亇亰乢乢乢乢乢乢乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乢乢乩乩乩") (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乢乢乩乩乩亇亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩")
                        wleaf
                      )
                      (ℓ "京") (ℓ "买京买")
                      wleaf
                    )
                    (ℓ "亞亪") (ℓ "亪亞")
                    (wnode
                      wleaf
                      (ℓ "丹井") (ℓ "亮丹")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "亠丯") (ℓ "丯亠")
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京丩") (ℓ "丩京")
                        wleaf
                      )
                      (ℓ "亨丯") (ℓ "丯亨")
                      wleaf
                    )
                    (ℓ "丌亂") (ℓ "並亁並")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢举亓乹亓乺") (ℓ "亓乹亓乺丢举")
                        wleaf
                      )
                      (ℓ "亐亡") (ℓ "亡亐京")
                      wleaf
                    )
                  )
                  (ℓ "亘些乻些亘乻") (ℓ "亜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰丹") (ℓ "丹亜")
                        wleaf
                      )
                      (ℓ "东乺云") (ℓ "云东乺")
                      wleaf
                    )
                    (ℓ "丽丶亠丶丸亠") (ℓ "丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亠亚") (ℓ "亚亜")
                        wleaf
                      )
                      (ℓ "五也") (ℓ "也亜五")
                      wleaf
                    )
                  )
                )
                (ℓ "五乇") (ℓ "乇五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘乀") (ℓ "乀亰")
                        wleaf
                      )
                      (ℓ "乎井") (ℓ "井乎")
                      wleaf
                    )
                    (ℓ "丷亣") (ℓ "亣丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丶亳") (ℓ "亳丶")
                        wleaf
                      )
                      (ℓ "五亭亠") (ℓ "亭五")
                      wleaf
                    )
                  )
                  (ℓ "乘亝") (ℓ "亍乘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亠亞") (ℓ "亞亰")
                        wleaf
                      )
                      (ℓ "乄亪") (ℓ "亪乄")
                      wleaf
                    )
                    (ℓ "举亞") (ℓ "亞举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢丯亜丯丱亜") (ℓ "丢")
                        wleaf
                      )
                      (ℓ "乒井") (ℓ "井乒")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜乺") (ℓ "乺亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丳亢") (ℓ "亢丳")
                        wleaf
                      )
                      (ℓ "了井") (ℓ "井了")
                      wleaf
                    )
                    (ℓ "亜亠亱") (ℓ "亱亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亟") (ℓ "亟买亳")
                        wleaf
                      )
                      (ℓ "二之亪个五") (ℓ "之亪二")
                      wleaf
                    )
                  )
                  (ℓ "了亡") (ℓ "亡了")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽亏") (ℓ "亏丽")
                        wleaf
                      )
                      (ℓ "亠丫") (ℓ "丫京")
                      wleaf
                    )
                    (ℓ "亜並丽並") (ℓ "並丽並亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠乻") (ℓ "乻亠")
                        wleaf
                      )
                      (ℓ "亁丽丽亁丢") (ℓ "亀")
                      wleaf
                    )
                  )
                )
                (ℓ "亡亡亭") (ℓ "亭")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亄二五二亄二丢亨亝亨亨丨亝亨亨丩二二亄二二五二二亄") (ℓ "亄二五二亄二丢亨亝亨亨丨亝亨亨丩二二亄二二五二二亄二")
                        wleaf
                      )
                      (ℓ "丌亁丢亮丶亮丷") (ℓ "亮丶亮丷丌亁丢")
                      wleaf
                    )
                    (ℓ "五亗") (ℓ "亗五个")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亣互亯") (ℓ "亯互")
                        wleaf
                      )
                      (ℓ "亁亄") (ℓ "亄亁")
                      wleaf
                    )
                  )
                  (ℓ "亠丱") (ℓ "丱亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽亚") (ℓ "亚丽")
                        wleaf
                      )
                      (ℓ "亠亰亝") (ℓ "亝亠")
                      wleaf
                    )
                    (ℓ "五不") (ℓ "不井")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亘亟") (ℓ "亟亠")
                        wleaf
                      )
                      (ℓ "乖亝") (ℓ "亝乖")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亞亞") []
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亝丨亝丩亪丯亪丰") (ℓ "亪丯亪丰亝丨亝丩")
                        wleaf
                      )
                      (ℓ "井並亄並") (ℓ "並亄並井")
                      wleaf
                    )
                    (ℓ "五亭") (ℓ "亭五亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽与中与") (ℓ "与中与丽")
                        wleaf
                      )
                      (ℓ "亨") (ℓ "井亨井")
                      wleaf
                    )
                  )
                  (ℓ "乳亡") (ℓ "亡乳")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亀") (ℓ "亀亰")
                        wleaf
                      )
                      (ℓ "丷並") (ℓ "並丷")
                      wleaf
                    )
                    (ℓ "丽並丢並") (ℓ "並丢並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹互") (ℓ "互乹")
                        wleaf
                      )
                      (ℓ "五") (ℓ "争五争")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亝") (ℓ "亝亜乫")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亁") (ℓ "丸亁丸亠")
                        wleaf
                      )
                      (ℓ "乥亝") (ℓ "亡乥")
                      wleaf
                    )
                    (ℓ "亨串") (ℓ "串五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丘临上") (ℓ "丘临上亜")
                        wleaf
                      )
                      (ℓ "丽乩") (ℓ "乩丽")
                      wleaf
                    )
                  )
                  (ℓ "亜") (ℓ "亠亢乤亢亠乤")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亡亰") (ℓ "亡亘")
                        wleaf
                      )
                      (ℓ "也亜亜") (ℓ "也")
                      wleaf
                    )
                    (ℓ "亙並乹並") (ℓ "並乹並亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乺丘临上") (ℓ "丘临上乺")
                        wleaf
                      )
                      (ℓ "亠丞") (ℓ "丞亢亠亠")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "井井") []
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亇二並") (ℓ "並二丘亇丢二")
                        wleaf
                      )
                      (ℓ "亏亞") (ℓ "亞亏")
                      wleaf
                    )
                    (ℓ "亠亳") (ℓ "亳亘亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五井丸井五丸") (ℓ "京")
                        wleaf
                      )
                      (ℓ "丞井") (ℓ "井丞")
                      wleaf
                    )
                  )
                  (ℓ "亜丩") (ℓ "丩亜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亮") (ℓ "亮丩")
                        wleaf
                      )
                      (ℓ "乩亢") (ℓ "亢乩")
                      wleaf
                    )
                    (ℓ "乩亝") (ℓ "亝乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亟") (ℓ "亟丱亜")
                        wleaf
                      )
                      (ℓ "乽亞") (ℓ "亞乽亚")
                      wleaf
                    )
                  )
                )
                (ℓ "亠") (ℓ "丽乽举乽丶")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亨亝亨亨丨亝亨亨丩亖") (ℓ "亨亝亨亨丨亝亨亨丩亖亜")
                        wleaf
                      )
                      (ℓ "东乺亙") (ℓ "亙东乺")
                      wleaf
                    )
                    (ℓ "串亩") (ℓ "亖串")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五与中与") (ℓ "与中与五")
                        wleaf
                      )
                      (ℓ "亠五亓") (ℓ "亓亠")
                      wleaf
                    )
                  )
                  (ℓ "丽亡") (ℓ "亡丽乹亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "上") (ℓ "並丽並丽")
                        wleaf
                      )
                      (ℓ "丯书亲") (ℓ "书亲丯")
                      wleaf
                    )
                    (ℓ "亠") (ℓ "丬亠丬")
                    (wnode
                      wleaf
                      (ℓ "买京京") (ℓ "买")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "二乕") (ℓ "乕二")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘亢") (ℓ "亢丘")
                        wleaf
                      )
                      (ℓ "亐乽") (ℓ "乽亐")
                      wleaf
                    )
                    (ℓ "了亙") (ℓ "亙了亡")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乺亓乹亓乺") (ℓ "亓乹亓乺乺")
                        wleaf
                      )
                      (ℓ "五京五京五") (ℓ "五")
                      wleaf
                    )
                  )
                  (ℓ "亜亡") (ℓ "亡亜亰")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "串亳") (ℓ "亣串")
                        wleaf
                      )
                      (ℓ "五亮丶") (ℓ "亮丶五")
                      wleaf
                    )
                    (ℓ "争五五") (ℓ "争")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京互亠") (ℓ "互亠京亠")
                        wleaf
                      )
                      (ℓ "丽亮丶亮丷") (ℓ "亮丶亮丷丽")
                      wleaf
                    )
                  )
                )
                (ℓ "亜") (ℓ "丽乭举乭丯")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乜亲") (ℓ "亲乜")
                        wleaf
                      )
                      (ℓ "二亝") (ℓ "亝二亨")
                      wleaf
                    )
                    (ℓ "丳享") (ℓ "享丳亗")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰亳") (ℓ "亳丰")
                        wleaf
                      )
                      (ℓ "云亭") (ℓ "亡亭云")
                      wleaf
                    )
                  )
                  (ℓ "井亡") (ℓ "亡井")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亚亠") (ℓ "亚亰")
                        wleaf
                      )
                      (ℓ "丫亟") (ℓ "享丫")
                      wleaf
                    )
                    (ℓ "亙並乩並") (ℓ "並乩並亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亣") (ℓ "亣亐")
                        wleaf
                      )
                      (ℓ "之井井") (ℓ "之")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五亮丨丶五") (ℓ "亮丨丶")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乙亓亓") (ℓ "乙")
                        wleaf
                      )
                      (ℓ "亝並亇並") (ℓ "並亇並亝")
                      wleaf
                    )
                    (ℓ "亐乕") (ℓ "乕亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亟亟") []
                        wleaf
                      )
                      (ℓ "争亝亝") (ℓ "争")
                      wleaf
                    )
                  )
                  (ℓ "乎亡") (ℓ "亡乎")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亪") (ℓ "亪丩")
                        wleaf
                      )
                      (ℓ "丽亪") (ℓ "亪丽")
                      wleaf
                    )
                    (ℓ "上乕五乕乗五") (ℓ "上")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乗亐亣") (ℓ "亣乗")
                        wleaf
                      )
                      (ℓ "乽亚") (ℓ "亚乽")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乪") (ℓ "乪亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠专") (ℓ "专亠")
                        wleaf
                      )
                      (ℓ "亲乎亲乏丂丣") (ℓ "丂丣亲乎亲乏")
                      wleaf
                    )
                    (ℓ "亰丷") (ℓ "丷亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亣亐") (ℓ "亣京")
                        wleaf
                      )
                      (ℓ "亁么") (ℓ "么亁")
                      wleaf
                    )
                  )
                  (ℓ "丷亡") (ℓ "亡丷乺亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐丨亐五亮丶") (ℓ "亮丶丨五")
                        wleaf
                      )
                      (ℓ "之五五") (ℓ "之")
                      wleaf
                    )
                    (ℓ "亭並亁並") (ℓ "並亁並亭")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亣") (ℓ "亣五亐")
                        wleaf
                      )
                      (ℓ "京丽") (ℓ "丽京")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜亞丿") (ℓ "亞亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亢五") (ℓ "亢京")
                        wleaf
                      )
                      (ℓ "丷並亇並") (ℓ "並亇並丷")
                      wleaf
                    )
                    (ℓ "乙二二") (ℓ "乙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓乹亓乺") (ℓ "亮丶亮丷")
                        wleaf
                      )
                      (ℓ "五乒") (ℓ "乒五")
                      wleaf
                    )
                  )
                  (ℓ "五丯") (ℓ "丯五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为亞亞") (ℓ "为")
                        wleaf
                      )
                      (ℓ "亢亮") (ℓ "亮亢")
                      wleaf
                    )
                    (ℓ "丽並丽並") (ℓ "並丽並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亓") (ℓ "亓五亠")
                        wleaf
                      )
                      (ℓ "丨亪") (ℓ "亪丨")
                      wleaf
                    )
                  )
                )
                (ℓ "亜乣") (ℓ "乣亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了井井") (ℓ "了")
                        wleaf
                      )
                      (ℓ "丽並") (ℓ "並上举")
                      wleaf
                    )
                    (ℓ "举东亢丝") (ℓ "亢亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乫二亜二") (ℓ "乫亜")
                        wleaf
                      )
                      (ℓ "丽乇") (ℓ "乇丽")
                      wleaf
                    )
                  )
                  (ℓ "丌亠") (ℓ "亡丌")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亰") (ℓ "亡亘亡")
                        wleaf
                      )
                      (ℓ "亜二亜二亜") (ℓ "亜")
                      wleaf
                    )
                    (ℓ "亄並亁並") (ℓ "並亁並亄")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢丨五丨个五") (ℓ "丢")
                        wleaf
                      )
                      (ℓ "乥亟") (ℓ "亣乥")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五井") (ℓ "井乗五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "亀亨亀")
                        wleaf
                      )
                      (ℓ "亮丶亮丷並亊並") (ℓ "並亊並亮丶亮丷")
                      wleaf
                    )
                    (ℓ "两亠严") (ℓ "亣")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五个") (ℓ "亗五亗")
                        wleaf
                      )
                      (ℓ "亜亨") (ℓ "亨亜")
                      wleaf
                    )
                  )
                  (ℓ "亃亠亠") (ℓ "亃")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五丙") (ℓ "丙五")
                        wleaf
                      )
                      (ℓ "五丱") (ℓ "丱五")
                      wleaf
                    )
                    (ℓ "亮丶亮丷並乕並") (ℓ "並乕並亮丶亮丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亚") (ℓ "亚亠亜")
                        wleaf
                      )
                      (ℓ "争云") (ℓ "云争井")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乖") (ℓ "乖亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "串亲") (ℓ "亢串")
                        wleaf
                      )
                      (ℓ "丘亇丢亝") (ℓ "亝丘亇丢")
                      wleaf
                    )
                    (ℓ "乕亓") (ℓ "亓乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄亣") (ℓ "亣乄亯")
                        wleaf
                      )
                      (ℓ "两乾东") (ℓ "两亣亠丿乾丿东")
                      wleaf
                    )
                  )
                  (ℓ "乕亡") (ℓ "亡乕")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "亏五亏")
                        wleaf
                      )
                      (ℓ "五买") (ℓ "买京五")
                      wleaf
                    )
                    (ℓ "京丬") (ℓ "丬亠京")
                    (wnode
                      wleaf
                      (ℓ "二") (ℓ "乭二乭")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (ℓ "亠丨") (ℓ "丨亠")
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亝亲些") (ℓ "些亝")
                        wleaf
                      )
                      (ℓ "亘乩") (ℓ "乩亘")
                      wleaf
                    )
                    (ℓ "上举") (ℓ "並丽並")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢举") (ℓ "与丽与")
                        wleaf
                      )
                      (ℓ "亐亠亐亠亐") (ℓ "亐")
                      wleaf
                    )
                  )
                  (ℓ "亠亰") (ℓ "亰亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亞亱") (ℓ "亱亞")
                        wleaf
                      )
                      (ℓ "乇上举") (ℓ "上举乇")
                      wleaf
                    )
                    (ℓ "丽亣") (ℓ "亣丽丶亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亯") (ℓ "亯买")
                        wleaf
                      )
                      (ℓ "丽亓") (ℓ "亓丽")
                      wleaf
                    )
                  )
                )
                (ℓ "五丞") (ℓ "丞五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰乀") (ℓ "乀亘")
                        wleaf
                      )
                      (ℓ "乭井") (ℓ "井乭亍")
                      wleaf
                    )
                    (ℓ "亨亀") (ℓ "亀亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞亗") (ℓ "亗丞")
                        wleaf
                      )
                      (ℓ "亜井") (ℓ "井亨亜")
                      wleaf
                    )
                  )
                  (ℓ "乙亍亍") (ℓ "乙")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亁亂") []
                        wleaf
                      )
                      (ℓ "京买") (ℓ "买京")
                      wleaf
                    )
                    (ℓ "乪亞") (ℓ "亞乪举亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢亟") (ℓ "亟丢丯亜")
                        wleaf
                      )
                      (ℓ "乽井") (ℓ "井乽云")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜丟") (ℓ "丟亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭亢") (ℓ "亢乭些")
                        wleaf
                      )
                      (ℓ "亘亝亰") (ℓ "亝亘")
                      wleaf
                    )
                    (ℓ "乘亢") (ℓ "亓乘")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亟") (ℓ "亟五二")
                        wleaf
                      )
                      (ℓ "五京亡") (ℓ "亡五")
                      wleaf
                    )
                  )
                  (ℓ "五五") []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞丽乽举乽丶丟") (ℓ "亢")
                        wleaf
                      )
                      (ℓ "亜乄") (ℓ "乄亨亜")
                      wleaf
                    )
                    (ℓ "亇並丽並") (ℓ "並丽並亇")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯享") (ℓ "享丯")
                        wleaf
                      )
                      (ℓ "亐亁亐並") (ℓ "並亐丌亁丢亐")
                      wleaf
                    )
                  )
                )
                (ℓ "云亡") (ℓ "亡云")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亄二亨二亄二丢五亪五五丯亪五五丰二二亄二二亨二二亄") (ℓ "亄二亨二亄二丢五亪五五丯亪五五丰二二亄二二亨二二亄二")
                        wleaf
                      )
                      (ℓ "亜东乺") (ℓ "东乺亜")
                      wleaf
                    )
                    (ℓ "亠亢") (ℓ "亢亠丿")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亣亯") (ℓ "亯亣")
                        wleaf
                      )
                      (ℓ "亁乹") (ℓ "乹亁")
                      wleaf
                    )
                  )
                  (ℓ "亠乄京") (ℓ "乄亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亚") (ℓ "亚亰亠")
                        wleaf
                      )
                      (ℓ "亠亲亜") (ℓ "亲亠")
                      wleaf
                    )
                    (ℓ "丽乕五乕乗五") (ℓ "丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亯亐") (ℓ "亯五")
                        wleaf
                      )
                      (ℓ "亘亝") (ℓ "亝亰亘")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "举世") (ℓ "世举")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽些") (ℓ "些丽")
                        wleaf
                      )
                      (ℓ "亜乼") (ℓ "乼亘")
                      wleaf
                    )
                    (ℓ "乬亙") (ℓ "亡乬")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢举与") (ℓ "与丽")
                        wleaf
                      )
                      (ℓ "乕云") (ℓ "云乕")
                      wleaf
                    )
                  )
                  (ℓ "二乙") (ℓ "乙二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘丽乭举乭丯丙") (ℓ "亞")
                        wleaf
                      )
                      (ℓ "丶並") (ℓ "並丶")
                      wleaf
                    )
                    (ℓ "丶乼") (ℓ "乼丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亗亯") (ℓ "亯亗")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "乽亐乽")
                      wleaf
                    )
                  )
                )
                (ℓ "亜乇") (ℓ "乇亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亁二二") (ℓ "二亁")
                        wleaf
                      )
                      (ℓ "亐京") (ℓ "京亐")
                      wleaf
                    )
                    (ℓ "五串") (ℓ "串亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亯与上与") (ℓ "与上与亯")
                        wleaf
                      )
                      (ℓ "丢亮丶亮丷") (ℓ "亮丶亮丷丢")
                      wleaf
                    )
                  )
                  (ℓ "乑亗") (ℓ "亣乑")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二井") (ℓ "井二亨")
                        wleaf
                      )
                      (ℓ "亜亙") (ℓ "亙亜亰")
                      wleaf
                    )
                    (ℓ "亮丶亮丷並乹並") (ℓ "並乹並亮丶亮丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰亞") (ℓ "亞丰举亜")
                        wleaf
                      )
                      (ℓ "乭亍") (ℓ "亍乭")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丌五不") (ℓ "井")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亃亢亢") (ℓ "亃")
                        wleaf
                      )
                      (ℓ "乙亞") (ℓ "亞乙亏")
                      wleaf
                    )
                    (ℓ "亜亝丸亝亜丸") (ℓ "亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亗亟") (ℓ "亟亗")
                        wleaf
                      )
                      (ℓ "乩井") (ℓ "井乩")
                      wleaf
                    )
                  )
                  (ℓ "亠乬") (ℓ "乬亘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乖亢") (ℓ "亢乖")
                        wleaf
                      )
                      (ℓ "亘亢") (ℓ "亢亘亜")
                      wleaf
                    )
                    (ℓ "举乪亜乪乫亜") (ℓ "举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亗") (ℓ "亗个五")
                        wleaf
                      )
                      (ℓ "争亞") (ℓ "亞争")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乻") (ℓ "亡亠亡")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜") (ℓ "亰亜亰")
                        wleaf
                      )
                      (ℓ "世乪亙") (ℓ "亙世乪")
                      wleaf
                    )
                    (ℓ "乜享享") (ℓ "乜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞主上亣") (ℓ "亣丞主上")
                        wleaf
                      )
                      (ℓ "亠丸亊丸") (ℓ "亊亠")
                      wleaf
                    )
                  )
                  (ℓ "乣亡") (ℓ "亡乣")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇亨") (ℓ "乇亝亨亝")
                        wleaf
                      )
                      (ℓ "亪五五") (ℓ "亪")
                      wleaf
                    )
                    (ℓ "丬亞") (ℓ "亞丬")
                    (wnode
                      wleaf
                      (ℓ "为亲") (ℓ "亲为")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "个亡") (ℓ "亡个京")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亢丿") (ℓ "亢亠")
                        wleaf
                      )
                      (ℓ "亐乖") (ℓ "乖亐")
                      wleaf
                    )
                    (ℓ "五么") (ℓ "么五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五乒五亓") (ℓ "乒亓")
                        wleaf
                      )
                      (ℓ "乕亏") (ℓ "亏乕")
                      wleaf
                    )
                  )
                  (ℓ "亃亡") (ℓ "亡亃")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乜亲亲") (ℓ "乜")
                        wleaf
                      )
                      (ℓ "亜丘亇丢") (ℓ "丘亇丢亜")
                      wleaf
                    )
                    (ℓ "丽亲") (ℓ "亲丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丱") (ℓ "亟亜亟")
                        wleaf
                      )
                      (ℓ "五") (ℓ "亮丶亮丷亮丶亮丷")
                      wleaf
                    )
                  )
                )
                (ℓ "亝亝亲") (ℓ "亲")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁亲") (ℓ "亲乁些")
                        wleaf
                      )
                      (ℓ "乬于") (ℓ "亖乬")
                      wleaf
                    )
                    (ℓ "亠举") (ℓ "举亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "与乗乗") (ℓ "与")
                        wleaf
                      )
                      (ℓ "亘书亲丱亜") (ℓ "书亲亘")
                      wleaf
                    )
                  )
                  (ℓ "二井亨") (ℓ "井二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亢") (ℓ "亢丩")
                        wleaf
                      )
                      (ℓ "京亠京亠京") (ℓ "京")
                      wleaf
                    )
                    (ℓ "丷並乩並") (ℓ "並乩並丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏亣") (ℓ "亣乏")
                        wleaf
                      )
                      (ℓ "亐井京") (ℓ "井亐")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五") (ℓ "乕乁乖乁丨")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯亢") (ℓ "亢丯")
                        wleaf
                      )
                      (ℓ "五乊") (ℓ "乊亜")
                      wleaf
                    )
                    (ℓ "亜亠亲") (ℓ "亲亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "两亜严") (ℓ "亟")
                        wleaf
                      )
                      (ℓ "争亙") (ℓ "亙争亝")
                      wleaf
                    )
                  )
                  (ℓ "乭亡") (ℓ "亡乭亙")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠") (ℓ "丽买举买乹")
                        wleaf
                      )
                      (ℓ "丞丽买举买乹丟") (ℓ "亢")
                      wleaf
                    )
                    (ℓ "上井") (ℓ "井上乕五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丙亣") (ℓ "亣丙")
                        wleaf
                      )
                      (ℓ "亜亇") (ℓ "丱亇丱亜")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亍") (ℓ "亍亜亨")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亓五") (ℓ "亓京")
                        wleaf
                      )
                      (ℓ "亜丢") (ℓ "丢亜")
                      wleaf
                    )
                    (ℓ "亰丳亠") (ℓ "丳亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亟") (ℓ "亟亨二")
                        wleaf
                      )
                      (ℓ "亁亭") (ℓ "亭亁")
                      wleaf
                    )
                  )
                  (ℓ "乹亡") (ℓ "亡乹")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亡京") (ℓ "亡")
                        wleaf
                      )
                      (ℓ "五云") (ℓ "云五京")
                      wleaf
                    )
                    (ℓ "亜丌") (ℓ "丌亝")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亯") (ℓ "亯五亐")
                        wleaf
                      )
                      (ℓ "亝亲") (ℓ "亲亝")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜亞") (ℓ "亞亜丿")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭些") (ℓ "些乭")
                        wleaf
                      )
                      (ℓ "亜丙") (ℓ "丙亞")
                      wleaf
                    )
                    (ℓ "乙云") (ℓ "云乙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丐丩") (ℓ "丐丩亜")
                        wleaf
                      )
                      (ℓ "亠亙") (ℓ "亙亠亰")
                      wleaf
                    )
                  )
                  (ℓ "二亏乫亏二乫") (ℓ "五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亞五") (ℓ "亞二")
                        wleaf
                      )
                      (ℓ "亘亢亜") (ℓ "亢亘")
                      wleaf
                    )
                    (ℓ "云並丢並") (ℓ "並丢並云")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乫亏") (ℓ "亏乫五")
                        wleaf
                      )
                      (ℓ "亜亪") (ℓ "亪亜五")
                      wleaf
                    )
                  )
                )
                (ℓ "亜丒") (ℓ "丒亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亍") (ℓ "亍了井")
                        wleaf
                      )
                      (ℓ "亜一丣") (ℓ "一丣亜")
                      wleaf
                    )
                    (ℓ "亠丿") (ℓ "亢亠亢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乫二亗") (ℓ "亗乫")
                        wleaf
                      )
                      (ℓ "丽乏") (ℓ "乏丽")
                      wleaf
                    )
                  )
                  (ℓ "五") (ℓ "亠亢乐亢亠乐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亡亮") (ℓ "亮井亡")
                        wleaf
                      )
                      (ℓ "亜乙") (ℓ "乙二亜")
                      wleaf
                    )
                    (ℓ "乹並亁並") (ℓ "並亁並乹")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢亗") (ℓ "亗丢丨五")
                        wleaf
                      )
                      (ℓ "书亝亝") (ℓ "书")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五乗井五") (ℓ "井")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亀") (ℓ "亀京")
                        wleaf
                      )
                      (ℓ "乘亞") (ℓ "亏乘")
                      wleaf
                    )
                    (ℓ "亠乣") (ℓ "乣亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为亟亟") (ℓ "为")
                        wleaf
                      )
                      (ℓ "亠云") (ℓ "云亠京")
                      wleaf
                    )
                  )
                  (ℓ "亐乹") (ℓ "乹亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亡") (ℓ "亡京五")
                        wleaf
                      )
                      (ℓ "丱亪") (ℓ "亪丱五")
                      wleaf
                    )
                    (ℓ "亁並乕並") (ℓ "並乕並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亏五五") (ℓ "亏")
                        wleaf
                      )
                      (ℓ "亐乕乕") (ℓ "乕乕亐")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乒五") (ℓ "乒亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丳亢亢") (ℓ "丳")
                        wleaf
                      )
                      (ℓ "五丢") (ℓ "丢五")
                      wleaf
                    )
                    (ℓ "亠亓") (ℓ "亓亠五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亣") (ℓ "亣丬")
                        wleaf
                      )
                      (ℓ "亠乾") (ℓ "丿乾丿亠")
                      wleaf
                    )
                  )
                  (ℓ "丿乻乻") (ℓ "丿")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乩乩乩亇亇乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乩乩乩") (ℓ "亇乢丘乢丘乢东东东丂东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东丂乩乩乩亇亇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乩乩乩")
                        wleaf
                      )
                      (ℓ "五") (ℓ "为五为")
                      wleaf
                    )
                    (ℓ "京") (ℓ "乄京乄")
                    (wnode
                      wleaf
                      (ℓ "亠乭亘") (ℓ "乭亠")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "乺上亡下") (ℓ "亡亠")
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亝") (ℓ "亝亰亠")
                        wleaf
                      )
                      (ℓ "亮丶亮丷並亄並") (ℓ "並亄並亮丶亮丷")
                      wleaf
                    )
                    (ℓ "京丨") (ℓ "丨京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜乫") (ℓ "乫亜")
                        wleaf
                      )
                      (ℓ "亰为亜") (ℓ "为亰")
                      wleaf
                    )
                  )
                  (ℓ "亜乫") (ℓ "亝亜亝")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丹") (ℓ "丹亰")
                        wleaf
                      )
                      (ℓ "丌亁丢亭") (ℓ "亭丌亁丢")
                      wleaf
                    )
                    (ℓ "亨乜") (ℓ "乜亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜享") (ℓ "享亜二")
                        wleaf
                      )
                      (ℓ "享丽享举") (ℓ "享丽享举")
                      wleaf
                    )
                  )
                )
                (ℓ "乪亙") (ℓ "亙乪")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乀乀") []
                        wleaf
                      )
                      (ℓ "乭亍亍") (ℓ "乭")
                      wleaf
                    )
                    (ℓ "丽丶亠乽") (ℓ "乽丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五乳互") (ℓ "乳互五")
                        wleaf
                      )
                      (ℓ "亘书亲") (ℓ "书亲丱亜亘")
                      wleaf
                    )
                  )
                  (ℓ "乘亏") (ℓ "亞乘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丩亞") (ℓ "亞丩")
                        wleaf
                      )
                      (ℓ "亘亞亠") (ℓ "亞亘")
                      wleaf
                    )
                    (ℓ "世亞") (ℓ "亞世丽亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇与丽与") (ℓ "与丽与乇")
                        wleaf
                      )
                      (ℓ "乼井") (ℓ "云乼")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜丞") (ℓ "丞亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亄二二") (ℓ "二亄")
                        wleaf
                      )
                      (ℓ "也亝亝") (ℓ "也")
                      wleaf
                    )
                    (ℓ "京云") (ℓ "云京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "书亟") (ℓ "亟书")
                        wleaf
                      )
                      (ℓ "亙亲") (ℓ "亝亲亙")
                      wleaf
                    )
                  )
                  (ℓ "五亡") (ℓ "亡五京")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亏") (ℓ "亏五")
                        wleaf
                      )
                      (ℓ "京丫") (ℓ "丫亠")
                      wleaf
                    )
                    (ℓ "上举亮丶亮丷") (ℓ "亮丶亮丷上举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘亣") (ℓ "亣丘")
                        wleaf
                      )
                      (ℓ "五丒") (ℓ "丒亖五五")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乶") (ℓ "乶亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亝丨亝丩亄五亄丢亝丨亝亨丩二亄五亄二丢") (ℓ "亪丯亪丰亄亨亄丢亪丯亪五丰二亄亨亄二丢")
                        wleaf
                      )
                      (ℓ "亁並") (ℓ "並丌亁丢")
                      wleaf
                    )
                    (ℓ "亠亃") (ℓ "亃亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亣") (ℓ "亣亘亜")
                        wleaf
                      )
                      (ℓ "亁亊") (ℓ "亊亁")
                      wleaf
                    )
                  )
                  (ℓ "乜亰亰") (ℓ "乜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌乹为乺为丽不") (ℓ "亡")
                        wleaf
                      )
                      (ℓ "么亝") (ℓ "亝么")
                      wleaf
                    )
                    (ℓ "乎並亁並") (ℓ "並亁並乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乢亟") (ℓ "亟乢")
                        wleaf
                      )
                      (ℓ "亐亮") (ℓ "亮亐五")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜丶") (ℓ "丶亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亰亙") (ℓ "亙亠")
                        wleaf
                      )
                      (ℓ "亁並亇並") (ℓ "並亇並亁")
                      wleaf
                    )
                    (ℓ "丶亭") (ℓ "亭丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓乹亓乺一下") (ℓ "一下亓乹亓乺")
                        wleaf
                      )
                      (ℓ "亜乶") (ℓ "乶亠亜")
                      wleaf
                    )
                  )
                  (ℓ "亐乘") (ℓ "乘亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亓") (ℓ "亓五")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "亠亣乫亣亠乫")
                      wleaf
                    )
                    (ℓ "亜並丢並") (ℓ "並丢並亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯亞") (ℓ "亞丯丽亜")
                        wleaf
                      )
                      (ℓ "五乽") (ℓ "乽亐五")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亝乫") (ℓ "亝亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亁二並") (ℓ "並二丌亁丢二")
                        wleaf
                      )
                      (ℓ "乥亣") (ℓ "亟乥")
                      wleaf
                    )
                    (ℓ "五") (ℓ "丽乄举乄乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亳") (ℓ "亳亠亘")
                        wleaf
                      )
                      (ℓ "亄丽") (ℓ "丽亄")
                      wleaf
                    )
                  )
                  (ℓ "亜") (ℓ "丯了丰了丽")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乑井") (ℓ "亡乑")
                        wleaf
                      )
                      (ℓ "乹亙") (ℓ "亙乹")
                      wleaf
                    )
                    (ℓ "丢並亁並") (ℓ "並亁並丢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜上") (ℓ "上亜")
                        wleaf
                      )
                      (ℓ "亠丢") (ℓ "丢亠")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五乎") (ℓ "乎五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京乁亐") (ℓ "乁京")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "乙亐乙")
                      wleaf
                    )
                    (ℓ "亘亠亳") (ℓ "亳亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亳") (ℓ "亳买")
                        wleaf
                      )
                      (ℓ "亲亜亜") (ℓ "亲")
                      wleaf
                    )
                  )
                  (ℓ "亃亝") (ℓ "亝亃")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠些") (ℓ "些亠亜")
                        wleaf
                      )
                      (ℓ "乄亮亮") (ℓ "乄")
                      wleaf
                    )
                    (ℓ "亭並丽並") (ℓ "並丽並亭")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亣") (ℓ "亣亐五")
                        wleaf
                      )
                      (ℓ "为亞") (ℓ "亞为")
                      wleaf
                    )
                  )
                )
                (ℓ "二丽") (ℓ "丽二")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丳亲") (ℓ "亲丳亢")
                        wleaf
                      )
                      (ℓ "乏丌亁丢") (ℓ "丌亁丢乏")
                      wleaf
                    )
                    (ℓ "亠丸") (ℓ "乽亠乽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜享二") (ℓ "享亜")
                        wleaf
                      )
                      (ℓ "五亠五") (ℓ "亠")
                      wleaf
                    )
                  )
                  (ℓ "举亡") (ℓ "亡举乺亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩亇乩") (ℓ "乩亇亇亨乇乇乇乇乇乇乇丘乇丘乇丐丐丐丂丐乩乩乩乩乩乩乩乩乩乇丘乇丘乇丐丐丐丂乇乇乩乩乩")
                        wleaf
                      )
                      (ℓ "亜买亰") (ℓ "买亜")
                      wleaf
                    )
                    (ℓ "乹亞") (ℓ "亞乹")
                    (wnode
                      wleaf
                      (ℓ "买亝亲") (ℓ "亲买")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "亜") (ℓ "乩乁乪乁丯")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕亢") (ℓ "亢乕")
                        wleaf
                      )
                      (ℓ "书亝") (ℓ "亝书")
                      wleaf
                    )
                    (ℓ "五了") (ℓ "了五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "中与丽与") (ℓ "与丽与中")
                        wleaf
                      )
                      (ℓ "亜丿") (ℓ "亞亜亞")
                      wleaf
                    )
                  )
                  (ℓ "二乩") (ℓ "乩二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亃亏") (ℓ "亏亃亞")
                        wleaf
                      )
                      (ℓ "亜之") (ℓ "之五亜")
                      wleaf
                    )
                    (ℓ "举争") (ℓ "争举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京与") (ℓ "与京")
                        wleaf
                      )
                      (ℓ "亜乩") (ℓ "乩亜")
                      wleaf
                    )
                  )
                )
                (ℓ "亐丽") (ℓ "丽亐")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亀乁亀") (ℓ "乀")
                        wleaf
                      )
                      (ℓ "亐亡京") (ℓ "亡亐")
                      wleaf
                    )
                    (ℓ "亠丳") (ℓ "丳亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亟些亳") (ℓ "亳些")
                        wleaf
                      )
                      (ℓ "亜亡") (ℓ "亡亰亜")
                      wleaf
                    )
                  )
                  (ℓ "二亨") (ℓ "亨二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五乳") (ℓ "乳亠五")
                        wleaf
                      )
                      (ℓ "亜乶亠") (ℓ "乶亜")
                      wleaf
                    )
                    (ℓ "亜世乪") (ℓ "世乪亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亗二") (ℓ "亗亜")
                        wleaf
                      )
                      (ℓ "乊亗") (ℓ "亟乊")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "丨") (ℓ "亮丨丶五亮丷亮丶亮丷")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乙亓") (ℓ "亓乙")
                        wleaf
                      )
                      (ℓ "丽並亊並") (ℓ "並亊並丽")
                      wleaf
                    )
                    (ℓ "五") (ℓ "乕丬乖丬丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亗") (ℓ "亗京亐")
                        wleaf
                      )
                      (ℓ "乼亞") (ℓ "亚乼")
                      wleaf
                    )
                  )
                  (ℓ "亙亡") (ℓ "亡亙")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亚") (ℓ "亚亜亠")
                        wleaf
                      )
                      (ℓ "五") (ℓ "亜五亜")
                      wleaf
                    )
                    (ℓ "乎並丽並") (ℓ "並丽並乎")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乗亐五亐") (ℓ "乗五")
                        wleaf
                      )
                      (ℓ "亨亞五") (ℓ "亞亨")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亠") (ℓ "亠亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亖") (ℓ "亖亠京")
                        wleaf
                      )
                      (ℓ "五一丣") (ℓ "一丣五")
                      wleaf
                    )
                    (ℓ "乜亗") (ℓ "亗乜享")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亟亣") (ℓ "亣亟")
                        wleaf
                      )
                      (ℓ "个亄个个") (ℓ "个亄")
                      wleaf
                    )
                  )
                  (ℓ "丷乺亠乺乻亠") (ℓ "丷")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨五") (ℓ "丨亪五亪")
                        wleaf
                      )
                      (ℓ "亜也") (ℓ "也亜")
                      wleaf
                    )
                    (ℓ "么並亁並") (ℓ "並亁並么")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乩书些") (ℓ "书些乩")
                        wleaf
                      )
                      (ℓ "乪些") (ℓ "些乪")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "丨亮") (ℓ "亮丨")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些亢") (ℓ "亢些")
                        wleaf
                      )
                      (ℓ "之井") (ℓ "井之")
                      wleaf
                    )
                    (ℓ "亜亃") (ℓ "亃亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亟") (ℓ "亟亜丱")
                        wleaf
                      )
                      (ℓ "亠丸") (ℓ "丸亠")
                      wleaf
                    )
                  )
                  (ℓ "五丶") (ℓ "丶五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丹亟") (ℓ "亳丹")
                        wleaf
                      )
                      (ℓ "亘亜") (ℓ "亜亘")
                      wleaf
                    )
                    (ℓ "乩並丽並") (ℓ "並丽並乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五井丱井五丱") (ℓ "亨")
                        wleaf
                      )
                      (ℓ "亐亁亐亐") (ℓ "亐亁")
                      wleaf
                    )
                  )
                )
                (ℓ "云亡亭") (ℓ "亭云")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乬亖") (ℓ "于乬")
                        wleaf
                      )
                      (ℓ "亜丐乖") (ℓ "丐乖亜")
                      wleaf
                    )
                    (ℓ "举东") (ℓ "东举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "互亯") (ℓ "亯亣互")
                        wleaf
                      )
                      (ℓ "亁乕") (ℓ "乕亁")
                      wleaf
                    )
                  )
                  (ℓ "亠丬") (ℓ "丬亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "亰亘亰")
                        wleaf
                      )
                      (ℓ "亠") (ℓ "京亭个亭京个")
                      wleaf
                    )
                    (ℓ "亊並亁並") (ℓ "並亁並亊")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎与丽与") (ℓ "与丽与乎")
                        wleaf
                      )
                      (ℓ "亘亲") (ℓ "亲亘亜")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五丟") (ℓ "丟五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亀") (ℓ "亀亨二")
                        wleaf
                      )
                      (ℓ "亠井") (ℓ "井亠京")
                      wleaf
                    )
                    (ℓ "亣亣") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亗") (ℓ "亗亜二")
                        wleaf
                      )
                      (ℓ "亐亠亭亠") (ℓ "亭亠亐")
                      wleaf
                    )
                  )
                  (ℓ "亐乙") (ℓ "乙亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五京云") (ℓ "云五")
                        wleaf
                      )
                      (ℓ "亠丘") (ℓ "丘亠")
                      wleaf
                    )
                    (ℓ "五丐乖") (ℓ "丐乖五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亚亠亠") (ℓ "亚")
                        wleaf
                      )
                      (ℓ "乼云") (ℓ "井乼")
                      wleaf
                    )
                  )
                )
                (ℓ "乒五五") (ℓ "乒")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "串亣") (ℓ "亳串")
                        wleaf
                      )
                      (ℓ "亭乇亭么丂丣") (ℓ "丂丣亭乇亭么")
                      wleaf
                    )
                    (ℓ "五乜") (ℓ "乜亨五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亣") (ℓ "亣乳")
                        wleaf
                      )
                      (ℓ "亨乾东亨丠") (ℓ "丠亨两乾丂亨")
                      wleaf
                    )
                  )
                  (ℓ "亀亡") (ℓ "亡亀")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "亓乹亓乺亓乹亓乺")
                        wleaf
                      )
                      (ℓ "亰丰") (ℓ "丰亰")
                      wleaf
                    )
                    (ℓ "亨丫") (ℓ "丫亜")
                    (wnode
                      wleaf
                      (ℓ "五") (ℓ "了五了")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    [] []
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二五二五二") (ℓ "二")
                        wleaf
                      )
                      (ℓ "丫享") (ℓ "亟丫")
                      wleaf
                    )
                    (ℓ "亂") (ℓ "丽不丽丌丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜与丽与") (ℓ "与丽与亜")
                        wleaf
                      )
                      (ℓ "亜亱亠") (ℓ "亱亜")
                      wleaf
                    )
                  )
                  (ℓ "乩亍") (ℓ "亍乩")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乕亞") (ℓ "亞乕")
                        wleaf
                      )
                      (ℓ "上举亭") (ℓ "亭上举")
                      wleaf
                    )
                    (ℓ "亨丽") (ℓ "丽亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亯") (ℓ "亯丬亣")
                        wleaf
                      )
                      (ℓ "亰些亜") (ℓ "些亰")
                      wleaf
                    )
                  )
                )
                (ℓ "五乹") (ℓ "乹五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亨二亨二") (ℓ "二")
                        wleaf
                      )
                      (ℓ "了亠亠") (ℓ "了")
                      wleaf
                    )
                    (ℓ "亠") (ℓ "丶亀丷亀乹")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丷亗") (ℓ "亗丷")
                        wleaf
                      )
                      (ℓ "云亮") (ℓ "井亮云")
                      wleaf
                    )
                  )
                  (ℓ "亍亝") (ℓ "亝亍")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亁亠") (ℓ "亡亁")
                        wleaf
                      )
                      (ℓ "京丷") (ℓ "丷京")
                      wleaf
                    )
                    (ℓ "亁並乩並") (ℓ "並乩並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "举丰亜丰丱亜") (ℓ "举")
                        wleaf
                      )
                      (ℓ "争井") (ℓ "井争")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜丷") (ℓ "丷亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亢") (ℓ "亢京五")
                        wleaf
                      )
                      (ℓ "也井") (ℓ "井也亝")
                      wleaf
                    )
                    (ℓ "乘云") (ℓ "亡乘")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京为五") (ℓ "为京")
                        wleaf
                      )
                      (ℓ "个京亡") (ℓ "亡个")
                      wleaf
                    )
                  )
                  (ℓ "五") (ℓ "乗五乗")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亞亢") (ℓ "亢亞")
                        wleaf
                      )
                      (ℓ "亨乄") (ℓ "乄亨")
                      wleaf
                    )
                    (ℓ "亄並丽並") (ℓ "並丽並亄")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亳亘") (ℓ "亳亠")
                        wleaf
                      )
                      (ℓ "丌亁丢") (ℓ "丌亝亜丱亁丱丢")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亡亰") (ℓ "亡亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜") (ℓ "亜")
                        wleaf
                      )
                      (ℓ "东乺亮丶亮丷") (ℓ "亮丶亮丷东乺")
                      wleaf
                    )
                    (ℓ "亠") (ℓ "乹乁乺乁丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丶亯") (ℓ "亯丶")
                        wleaf
                      )
                      (ℓ "丷乩") (ℓ "乩丷")
                      wleaf
                    )
                  )
                  (ℓ "亠个") (ℓ "个亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亮五五") (ℓ "亮")
                        wleaf
                      )
                      (ℓ "乙亐亐") (ℓ "乙")
                      wleaf
                    )
                    (ℓ "丽井") (ℓ "井丽乕五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亳") (ℓ "亳亜亘")
                        wleaf
                      )
                      (ℓ "亘") (ℓ "亰亳丿亳亰丿")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "举乏") (ℓ "乏举")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "京五京")
                        wleaf
                      )
                      (ℓ "乼亝") (ℓ "亙乼")
                      wleaf
                    )
                    (ℓ "五京") (ℓ "京五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽与丽与") (ℓ "与丽与丽")
                        wleaf
                      )
                      (ℓ "亜井亨") (ℓ "井亜")
                      wleaf
                    )
                  )
                  (ℓ "乙亡") (ℓ "亡乙云")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亃亞亞") (ℓ "亃")
                        wleaf
                      )
                      (ℓ "五乒五亮") (ℓ "乒亮")
                      wleaf
                    )
                    (ℓ "亜亝丸亝亜丸乼") (ℓ "乼亘亙丿亙亘丿")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亗") (ℓ "亗二亜")
                        wleaf
                      )
                      (ℓ "乽亘亘") (ℓ "乽")
                      wleaf
                    )
                  )
                )
                (ℓ "亝亝") []
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乀亚") (ℓ "亱乀")
                        wleaf
                      )
                      (ℓ "乶亡亡") (ℓ "乶")
                      wleaf
                    )
                    (ℓ "丳亗亗") (ℓ "丳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五与上与") (ℓ "与上与五")
                        wleaf
                      )
                      (ℓ "亁丢") (ℓ "丢亁")
                      wleaf
                    )
                  )
                  (ℓ "亠乑") (ℓ "乑五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亍丿亍二丿") (ℓ "亨")
                        wleaf
                      )
                      (ℓ "五也亜") (ℓ "也五")
                      wleaf
                    )
                    (ℓ "亜並乹並") (ℓ "並乹並亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "临与丽与") (ℓ "与丽与临")
                        wleaf
                      )
                      (ℓ "亠亝亰") (ℓ "亝亠")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亘丽") (ℓ "丽亘")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁亓") (ℓ "亓乁")
                        wleaf
                      )
                      (ℓ "亠") (ℓ "亃亠亃")
                      wleaf
                    )
                    (ℓ "丩丢亗丣") (ℓ "亗五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丶亗") (ℓ "亗丶")
                        wleaf
                      )
                      (ℓ "丟井") (ℓ "井丟")
                      wleaf
                    )
                  )
                  (ℓ "乬亡") (ℓ "亙乬")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亞亢亲") (ℓ "亲亞")
                        wleaf
                      )
                      (ℓ "丬亢") (ℓ "亢丬")
                      wleaf
                    )
                    (ℓ "乪亝") (ℓ "亝乪")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亗个") (ℓ "亗五")
                        wleaf
                      )
                      (ℓ "争亞亞") (ℓ "争")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乻亡") (ℓ "亡亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亰些") (ℓ "些亰")
                        wleaf
                      )
                      (ℓ "乎上举") (ℓ "上举乎")
                      wleaf
                    )
                    (ℓ "之亗") (ℓ "亗之")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠丸亣亠") (ℓ "亣")
                        wleaf
                      )
                      (ℓ "亐亊亐亮丶亮丷") (ℓ "亮丶亮丷亊")
                      wleaf
                    )
                  )
                  (ℓ "丸乻乻") (ℓ "丸")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽亁丽") (ℓ "丽亁亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽")
                        wleaf
                      )
                      (ℓ "丘亡") (ℓ "亡丘")
                      wleaf
                    )
                    (ℓ "亜") (ℓ "丯亀丰亀乩")
                    (wnode
                      wleaf
                      (ℓ "亝亲亲") (ℓ "亝")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "亐互乗互亐乗") (ℓ "亠")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五二五二五") (ℓ "五")
                        wleaf
                      )
                      (ℓ "五亝") (ℓ "亝五亨")
                      wleaf
                    )
                    (ℓ "五乭二") (ℓ "乭五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亏") (ℓ "亏五亜")
                        wleaf
                      )
                      (ℓ "亰买") (ℓ "买亰")
                      wleaf
                    )
                  )
                  (ℓ "二") (ℓ "五亗乫亗五乫")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乜亢") (ℓ "亢乜亲")
                        wleaf
                      )
                      (ℓ "丒亄丢井") (ℓ "井丒亄丢")
                      wleaf
                    )
                    (ℓ "亐争五") (ℓ "争亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丱亟") (ℓ "亟亜")
                        wleaf
                      )
                      (ℓ "丽亁丽亁丽亁") (ℓ "丢丢丢")
                      wleaf
                    )
                  )
                )
                (ℓ "亙亝") (ℓ "亝亙")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亀京京") (ℓ "亀")
                        wleaf
                      )
                      (ℓ "五乬") (ℓ "乬二")
                      wleaf
                    )
                    (ℓ "丶举丷") (ℓ "举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五乗") (ℓ "乗五")
                        wleaf
                      )
                      (ℓ "丱亜") (ℓ "丱亨亜亨")
                      wleaf
                    )
                  )
                  (ℓ "乒亡") (ℓ "亡乒井")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乖亓") (ℓ "亓乖")
                        wleaf
                      )
                      (ℓ "京乄") (ℓ "乄京")
                      wleaf
                    )
                    (ℓ "丶並乩並") (ℓ "並乩並丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亣") (ℓ "亣京亐")
                        wleaf
                      )
                      (ℓ "之亝") (ℓ "亝之井")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亐丨亐五亮丶") (ℓ "亮丨丶五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乙亢") (ℓ "亢乙亓")
                        wleaf
                      )
                      (ℓ "乊井") (ℓ "亝乊")
                      wleaf
                    )
                    (ℓ "亜") (ℓ "乩丳乪丳丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒中上亗") (ℓ "亗丒中上")
                        wleaf
                      )
                      (ℓ "乽亐亐") (ℓ "乽")
                      wleaf
                    )
                  )
                  (ℓ "了五五") (ℓ "了")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亚亠") (ℓ "亚亜")
                        wleaf
                      )
                      (ℓ "亘乽") (ℓ "乽亘")
                      wleaf
                    )
                    (ℓ "举乖五乖乗五") (ℓ "举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亣") (ℓ "亣丨")
                        wleaf
                      )
                      (ℓ "亜丘") (ℓ "丘亞亜亜")
                      wleaf
                    )
                  )
                )
                (ℓ "亠书亜") (ℓ "书亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰些") (ℓ "些亰亜")
                        wleaf
                      )
                      (ℓ "丶丘亇丢") (ℓ "丘亇丢丶")
                      wleaf
                    )
                    (ℓ "丳亗") (ℓ "亗丳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亣与主与") (ℓ "与主与亣")
                        wleaf
                      )
                      (ℓ "亁乏") (ℓ "乏亁")
                      wleaf
                    )
                  )
                  (ℓ "亠亡") (ℓ "亡乻亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨") (ℓ "亍亨亍")
                        wleaf
                      )
                      (ℓ "亜之五") (ℓ "之亜")
                      wleaf
                    )
                    (ℓ "丽乩亜乩乫亜") (ℓ "丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亟") (ℓ "亟二")
                        wleaf
                      )
                      (ℓ "亨个") (ℓ "个亨")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亐") (ℓ "並亐並")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亡个亡亠个") (ℓ "京")
                        wleaf
                      )
                      (ℓ "亜丘") (ℓ "丘亞")
                      wleaf
                    )
                    (ℓ "亘亙丿亙亘丿") (ℓ "亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丐丩亓乹亓乺") (ℓ "亓乹亓乺丐丩")
                        wleaf
                      )
                      (ℓ "五乳亠") (ℓ "乳五")
                      wleaf
                    )
                  )
                  (ℓ "乘亓") (ℓ "亢乘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为亱") (ℓ "亱为亞")
                        wleaf
                      )
                      (ℓ "丬亮") (ℓ "亮丬亢")
                      wleaf
                    )
                    (ℓ "亙並丢並") (ℓ "並丢並亙")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乺与临与") (ℓ "与临与乺")
                        wleaf
                      )
                      (ℓ "亘争亜") (ℓ "争亘")
                      wleaf
                    )
                  )
                )
                (ℓ "亜专") (ℓ "专亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "井亖亝丨亝丩二亄五亄丢亁五亁二丢") (ℓ "亪亩亪丯亪丰二亄亨亄丢亇亨亇二丢")
                        wleaf
                      )
                      (ℓ "亦丂丣") (ℓ "丂丣亦")
                      wleaf
                    )
                    (ℓ "亠丿亢") (ℓ "亢亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰书些") (ℓ "书些乫亜亰")
                        wleaf
                      )
                      (ℓ "丽乎") (ℓ "乎丽")
                      wleaf
                    )
                  )
                  (ℓ "亘") (ℓ "亜亟乻亟亜乻")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "井京京") (ℓ "井")
                        wleaf
                      )
                      (ℓ "二") (ℓ "乙二乙")
                      wleaf
                    )
                    (ℓ "乩並亁並") (ℓ "並亁並乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "举丩五丩个五") (ℓ "举")
                        wleaf
                      )
                      (ℓ "二亝亨") (ℓ "亝二")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五井") (ℓ "井五乗")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亀些") (ℓ "些亀亲")
                        wleaf
                      )
                      (ℓ "亠亐亠亐亠") (ℓ "亠")
                      wleaf
                    )
                    (ℓ "亠乎") (ℓ "乎亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乜亳") (ℓ "亳乜")
                        wleaf
                      )
                      (ℓ "五乳亭") (ℓ "乳亭五")
                      wleaf
                    )
                  )
                  (ℓ "亐乺") (ℓ "乺亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亙亱") (ℓ "亡亱亙")
                        wleaf
                      )
                      (ℓ "丫亯") (ℓ "亣丫")
                      wleaf
                    )
                    (ℓ "丽並乕並") (ℓ "並乕並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亐亯") (ℓ "亯五")
                        wleaf
                      )
                      (ℓ "亐亄亐並") (ℓ "並亐丒亄丢亐")
                      wleaf
                    )
                  )
                )
                (ℓ "亠丩") (ℓ "丩亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亢亲") (ℓ "亲亢")
                        wleaf
                      )
                      (ℓ "丢亙") (ℓ "亙丢")
                      wleaf
                    )
                    (ℓ "五享二") (ℓ "享五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠丸") (ℓ "亣亠亣")
                        wleaf
                      )
                      (ℓ "亠两") (ℓ "两亣亠亠")
                      wleaf
                    )
                  )
                  (ℓ "丿亡") (ℓ "亡丿乻")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕亄亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕") (ℓ "亄乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乕乕乕亄亄丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一乕乕乕")
                        wleaf
                      )
                      (ℓ "亜亏五") (ℓ "亏亜")
                      wleaf
                    )
                    (ℓ "乄亪亪") (ℓ "乄")
                    (wnode
                      wleaf
                      (ℓ "丹亲") (ℓ "亝丹")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "丌亠不") (ℓ "亡")
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌乩乁乪乁丯不") (ℓ "亝")
                        wleaf
                      )
                      (ℓ "亜亝个亝亜个") (ℓ "亨")
                      wleaf
                    )
                    (ℓ "不亁") (ℓ "並亂並")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜与乫") (ℓ "与亜")
                        wleaf
                      )
                      (ℓ "乏亡") (ℓ "亡乏")
                      wleaf
                    )
                  )
                  (ℓ "亜乫亝") (ℓ "亝亜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丹亞") (ℓ "亱丹")
                        wleaf
                      )
                      (ℓ "么丌亁丢") (ℓ "丌亁丢么")
                      wleaf
                    )
                    (ℓ "亠亓五") (ℓ "亓亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亯") (ℓ "亯亐")
                        wleaf
                      )
                      (ℓ "五亜五亜五") (ℓ "五")
                      wleaf
                    )
                  )
                )
                (ℓ "亙亝亲") (ℓ "亲亙")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乀亱") (ℓ "亚乀")
                        wleaf
                      )
                      (ℓ "亍井") (ℓ "井亍")
                      wleaf
                    )
                    (ℓ "举丷亠丷丸亠") (ℓ "举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丷亳") (ℓ "亳丷")
                        wleaf
                      )
                      (ℓ "亭亠亠") (ℓ "亭")
                      wleaf
                    )
                  )
                  (ℓ "亜乘") (ℓ "乘二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丟亞") (ℓ "亞丟")
                        wleaf
                      )
                      (ℓ "丬亪") (ℓ "亪丬亞")
                      wleaf
                    )
                    (ℓ "乪举亜举丿亜") (ℓ "乪")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "互与丽与") (ℓ "与丽与互")
                        wleaf
                      )
                      (ℓ "乽云云") (ℓ "乽")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜乹") (ℓ "乹亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乭些些") (ℓ "乭")
                        wleaf
                      )
                      (ℓ "井亝") (ℓ "亝井")
                      wleaf
                    )
                    (ℓ "丶亱") (ℓ "亱丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乇亟") (ℓ "亟乇")
                        wleaf
                      )
                      (ℓ "丰亲") (ℓ "亲丰")
                      wleaf
                    )
                  )
                  (ℓ "二了五") (ℓ "了二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亢亜亜") (ℓ "亢")
                        wleaf
                      )
                      (ℓ "丫亮") (ℓ "亢丫")
                      wleaf
                    )
                    (ℓ "亜上举") (ℓ "上举亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨与") (ℓ "与亨")
                        wleaf
                      )
                      (ℓ "亀亮丶亮丷") (ℓ "亮丶五亮丷亐亁丽丽亁亐丢乕")
                      wleaf
                    )
                  )
                )
                (ℓ "亠云京") (ℓ "云亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二丢亨亝亨亨丨亝亨亨丩") (ℓ "丢亨亝亨亨丨亝亨亨丩二")
                        wleaf
                      )
                      (ℓ "亜丌亁丢") (ℓ "丌亁丢亜")
                      wleaf
                    )
                    (ℓ "五个亗五") (ℓ "亗")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜乽") (ℓ "乽亘亜")
                        wleaf
                      )
                      (ℓ "亁亇") (ℓ "亇亁")
                      wleaf
                    )
                  )
                  (ℓ "亠乜亰") (ℓ "乜亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠五亠五亠") (ℓ "亠")
                        wleaf
                      )
                      (ℓ "丟亝") (ℓ "亝丟")
                      wleaf
                    )
                    (ℓ "亲並亁並") (ℓ "並亁並亲")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丟亟") (ℓ "亟丟")
                        wleaf
                      )
                      (ℓ "五亨五") (ℓ "亨")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜並丱") (ℓ "並亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亭") (ℓ "亭亠五")
                        wleaf
                      )
                      (ℓ "丽並亇並") (ℓ "並亇並丽")
                      wleaf
                    )
                    (ℓ "五亠亭") (ℓ "亭五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "上与丽与") (ℓ "与丽与上")
                        wleaf
                      )
                      (ℓ "乳亭亮丶亮丷") (ℓ "亮丶亮丷乳亭")
                      wleaf
                    )
                  )
                  (ℓ "乙云云") (ℓ "乙")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亞亠亠") (ℓ "亞")
                        wleaf
                      )
                      (ℓ "丷亮丶亮丷") (ℓ "亮丶亮丷丷")
                      wleaf
                    )
                    (ℓ "亁並丢並") (ℓ "並丢並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乺互") (ℓ "互乺")
                        wleaf
                      )
                      (ℓ "亐争") (ℓ "争五亐")
                      wleaf
                    )
                  )
                )
                (ℓ "亜乫亝亜") (ℓ "亝")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌亁丢") (ℓ "丌亡亠丸亁丸丢")
                        wleaf
                      )
                      (ℓ "亜乥") (ℓ "乥亠")
                      wleaf
                    )
                    (ℓ "串亖") (ℓ "亩串")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五互亠") (ℓ "互五")
                        wleaf
                      )
                      (ℓ "丽乹") (ℓ "乹丽")
                      wleaf
                    )
                  )
                  (ℓ "五亖义亖五义") (ℓ "亜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳亡亡") (ℓ "乳")
                        wleaf
                      )
                      (ℓ "五云京") (ℓ "云五")
                      wleaf
                    )
                    (ℓ "云並乹並") (ℓ "並乹並云")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹丘临上") (ℓ "丘临上乹")
                        wleaf
                      )
                      (ℓ "亠亊") (ℓ "丸亊丸亠")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五並个") (ℓ "並五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "亪丯亪丰亪丯亪丰")
                        wleaf
                      )
                      (ℓ "乙亏亏") (ℓ "乙")
                      wleaf
                    )
                    (ℓ "五丳") (ℓ "丳五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丘临上亟") (ℓ "亟丘临上")
                        wleaf
                      )
                      (ℓ "亘乪") (ℓ "乪亘")
                      wleaf
                    )
                  )
                  (ℓ "亐") (ℓ "五亗乻亗五乻")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京丬亠") (ℓ "丬京")
                        wleaf
                      )
                      (ℓ "亃亢") (ℓ "亢亃")
                      wleaf
                    )
                    (ℓ "上乩亜乩乫亜") (ℓ "上")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亣亚亳") (ℓ "亳亚")
                        wleaf
                      )
                      (ℓ "丨亞") (ℓ "亞丨")
                      wleaf
                    )
                  )
                )
                (ℓ "二举") (ℓ "举二")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亝丨亝丩亖亝丨亝亨丩亖亜亪亩亪亪丯亪丰亪五亩亜亪五") []
                        wleaf
                      )
                      (ℓ "五东乺") (ℓ "东乺五")
                      wleaf
                    )
                    (ℓ "亠丸乽") (ℓ "乽亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亯") (ℓ "亯亠亐")
                        wleaf
                      )
                      (ℓ "亠五") (ℓ "亓亠亓")
                      wleaf
                    )
                  )
                  (ℓ "丽乹亠乹乻亠") (ℓ "丽")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕亄乕") (ℓ "乕亄亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕")
                        wleaf
                      )
                      (ℓ "亜为") (ℓ "为亜")
                      wleaf
                    )
                    (ℓ "乄亞") (ℓ "亞乄亪")
                    (wnode
                      wleaf
                      (ℓ "买亲") (ℓ "亲买亝")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "京亡") (ℓ "亡京")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乪亢") (ℓ "亢乪")
                        wleaf
                      )
                      (ℓ "乇亝") (ℓ "亝乇")
                      wleaf
                    )
                    (ℓ "五亡京") (ℓ "亡五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓乹亓乺与中与") (ℓ "与中与亓乹亓乺")
                        wleaf
                      )
                      (ℓ "亜丿亞") (ℓ "亞亜")
                      wleaf
                    )
                  )
                  (ℓ "二乪") (ℓ "乪二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乙亏") (ℓ "亏乙")
                        wleaf
                      )
                      (ℓ "乒亮亮丶亮丷") (ℓ "亮丶亮丷乒亮")
                      wleaf
                    )
                    (ℓ "丽争") (ℓ "争丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京亠互亠") (ℓ "互亠京")
                        wleaf
                      )
                      (ℓ "五乕") (ℓ "乕五")
                      wleaf
                    )
                  )
                )
                (ℓ "亐举") (ℓ "举亐")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁些些") (ℓ "乁")
                        wleaf
                      )
                      (ℓ "乶亝") (ℓ "亝乶亡")
                      wleaf
                    )
                    (ℓ "亠亗亐") (ℓ "亗亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "亟二亟")
                        wleaf
                      )
                      (ℓ "亜买") (ℓ "买亰亜")
                      wleaf
                    )
                  )
                  (ℓ "乒井井") (ℓ "乒")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠") (ℓ "乳亠乳")
                        wleaf
                      )
                      (ℓ "亠亮") (ℓ "亮五亠")
                      wleaf
                    )
                    (ℓ "亜並乩並") (ℓ "並乩並亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓亯") (ℓ "亯亗亓")
                        wleaf
                      )
                      (ℓ "乊亝") (ℓ "井乊")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五") (ℓ "亪五亪")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亡丱亡亠丱") (ℓ "亰")
                        wleaf
                      )
                      (ℓ "亜並亇並") (ℓ "並亇並亜")
                      wleaf
                    )
                    (ℓ "亨亍") (ℓ "亍亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜与临与") (ℓ "与临与亜")
                        wleaf
                      )
                      (ℓ "乼亙") (ℓ "亝乼")
                      wleaf
                    )
                  )
                  (ℓ "乶亡") (ℓ "亡乶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨丬亜") (ℓ "丬亨")
                        wleaf
                      )
                      (ℓ "亘乁") (ℓ "乁亘")
                      wleaf
                    )
                    (ℓ "亲並丽並") (ℓ "並丽並亲")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亐亣") (ℓ "亣五")
                        wleaf
                      )
                      (ℓ "争亚") (ℓ "亚争亞")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乩") (ℓ "乩亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒乕丬乖丬丽专") (ℓ "亖")
                        wleaf
                      )
                      (ℓ "亙一丣") (ℓ "一丣亙")
                      wleaf
                    )
                    (ℓ "丳亠亠") (ℓ "丳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亟") (ℓ "亟丨")
                        wleaf
                      )
                      (ℓ "五个亄个") (ℓ "亄五")
                      wleaf
                    )
                  )
                  (ℓ "乺亡") (ℓ "亡乺")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亮丶丨五") (ℓ "亮丶丨")
                        wleaf
                      )
                      (ℓ "亜亙亰") (ℓ "亙亜")
                      wleaf
                    )
                    (ℓ "乇並亁並") (ℓ "並亁並乇")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乪书些") (ℓ "书些乪")
                        wleaf
                      )
                      (ℓ "亝些") (ℓ "些亝亲")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜亞") (ℓ "亞丿亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁些") (ℓ "些乁")
                        wleaf
                      )
                      (ℓ "五") (ℓ "丨亃丩亃丽")
                      wleaf
                    )
                    (ℓ "亃云") (ℓ "云亃亡")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") (ℓ "与五乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢丨丨丨乕丒乕丒乕丢丢丢一乕乕丒乕丒乕丢丢丢一丨与")
                        wleaf
                      )
                      (ℓ "亠並丸") (ℓ "並亠")
                      wleaf
                    )
                  )
                  (ℓ "五丷") (ℓ "丷五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丹亱") (ℓ "亞丹")
                        wleaf
                      )
                      (ℓ "丬亢亢") (ℓ "丬")
                      wleaf
                    )
                    (ℓ "乕並丽並") (ℓ "並丽並乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "亨亪丱亪亨丱")
                        wleaf
                      )
                      (ℓ "五亐五亐五") (ℓ "五")
                      wleaf
                    )
                  )
                )
                (ℓ "亜乢") (ℓ "乢亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乬亍") (ℓ "井乬")
                        wleaf
                      )
                      (ℓ "丐乖亮丶亮丷") (ℓ "亮丶亮丷丐乖")
                      wleaf
                    )
                    (ℓ "举丝") (ℓ "丝举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰书些乫亜") (ℓ "书些亰")
                        wleaf
                      )
                      (ℓ "丽么") (ℓ "么丽")
                      wleaf
                    )
                  )
                  (ℓ "不亠") (ℓ "亡不")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乪井") (ℓ "井乪")
                        wleaf
                      )
                      (ℓ "亠") (ℓ "亰亱丱亱亰丱")
                      wleaf
                    )
                    (ℓ "亇並亁並") (ℓ "並亁並亇")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些与丽与") (ℓ "与丽与些")
                        wleaf
                      )
                      (ℓ "亐") (ℓ "京亯丿亯京丿")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五乏") (ℓ "乏五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁亀乁") (ℓ "乀")
                        wleaf
                      )
                      (ℓ "亘了亠") (ℓ "了亘")
                      wleaf
                    )
                    (ℓ "丷丢亣丣") (ℓ "亣亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "个五个")
                        wleaf
                      )
                      (ℓ "亐亭亠") (ℓ "亭亠亐亠")
                      wleaf
                    )
                  )
                  (ℓ "乙亝") (ℓ "亝乙亍")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京") (ℓ "亡京亡")
                        wleaf
                      )
                      (ℓ "亠丙") (ℓ "丙亠")
                      wleaf
                    )
                    (ℓ "五並乕並") (ℓ "並乕並五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亐亯") (ℓ "亯亠")
                        wleaf
                      )
                      (ℓ "争井井") (ℓ "争")
                      wleaf
                    )
                  )
                )
                (ℓ "五亠") (ℓ "亠五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰串") (ℓ "串亠")
                        wleaf
                      )
                      (ℓ "丞亊丢亡") (ℓ "亡丞亊丢")
                      wleaf
                    )
                    (ℓ "亨") (ℓ "乜亨乜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乢亣") (ℓ "亣乢")
                        wleaf
                      )
                      (ℓ "两乾一") (ℓ "两亣亠丿乾丿一")
                      wleaf
                    )
                  )
                  (ℓ "乪亡") (ℓ "亡乪")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亓乹") (ℓ "亓乹五")
                        wleaf
                      )
                      (ℓ "京五京五京") (ℓ "京")
                      wleaf
                    )
                    (ℓ "亠京亠京亠") (ℓ "亠")
                    (wnode
                      wleaf
                      (ℓ "亠了") (ℓ "了亠")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (ℓ "亠丰") (ℓ "丰亠")
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丌乩丳乪丳丽不") (ℓ "亝")
                        wleaf
                      )
                      (ℓ "丷乖") (ℓ "乖丷")
                      wleaf
                    )
                    (ℓ "下丽") (ℓ "並举並")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丢举") (ℓ "丢举亜")
                        wleaf
                      )
                      (ℓ "亜亰亡") (ℓ "亡亜")
                      wleaf
                    )
                  )
                  (ℓ "二于乗于二乗") (ℓ "亜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "买亱亱") (ℓ "买")
                        wleaf
                      )
                      (ℓ "丐乖云") (ℓ "云丐乖")
                      wleaf
                    )
                    (ℓ "丶亣") (ℓ "亣丶")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亣亣") (ℓ "丬")
                        wleaf
                      )
                      (ℓ "亜") (ℓ "也亜也")
                      wleaf
                    )
                  )
                )
                (ℓ "五亨") (ℓ "亨五")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乀些") (ℓ "亲乀")
                        wleaf
                      )
                      (ℓ "亘乭") (ℓ "乭亘")
                      wleaf
                    )
                    (ℓ "亠亣") (ℓ "亣丸亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些亜亜") (ℓ "些")
                        wleaf
                      )
                      (ℓ "丷亭") (ℓ "亭丷")
                      wleaf
                    )
                  )
                  (ℓ "二乘") (ℓ "乘亜")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亁丢") (ℓ "亂")
                        wleaf
                      )
                      (ℓ "京丶") (ℓ "丶京")
                      wleaf
                    )
                    (ℓ "亜") (ℓ "丽乜举乜乩")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯亟") (ℓ "亟丯")
                        wleaf
                      )
                      (ℓ "乇井") (ℓ "井乇")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜乕") (ℓ "乕亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亢") (ℓ "亢丨")
                        wleaf
                      )
                      (ℓ "乹井") (ℓ "井乹")
                      wleaf
                    )
                    (ℓ "亜亱") (ℓ "亱亜亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为五五") (ℓ "为")
                        wleaf
                      )
                      (ℓ "个五") (ℓ "个京五京")
                      wleaf
                    )
                  )
                  (ℓ "二") (ℓ "亜亟乗亟亜乗")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "举亏") (ℓ "亏举")
                        wleaf
                      )
                      (ℓ "亨亜亨亜亨") (ℓ "亨")
                      wleaf
                    )
                    (ℓ "亊並丽並") (ℓ "並丽並亊")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠与乻") (ℓ "与亠")
                        wleaf
                      )
                      (ℓ "亐丽丽") (ℓ "丽丽亐")
                      wleaf
                    )
                  )
                )
                (ℓ "乢亰") (ℓ "乢亡亰亡")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二丢五亪五五丯亪五五丰") (ℓ "丢五亪五五丯亪五五丰二")
                        wleaf
                      )
                      (ℓ "丌亁丢並") (ℓ "並亁")
                      wleaf
                    )
                    (ℓ "亠丿亢亠") (ℓ "亢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "亣亘亣")
                        wleaf
                      )
                      (ℓ "乹亮丶亮丷") (ℓ "亮丶亮丷乹")
                      wleaf
                    )
                  )
                  (ℓ "乄京京") (ℓ "乄")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨亏五") (ℓ "亏亨")
                        wleaf
                      )
                      (ℓ "二亜二亜二") (ℓ "二")
                      wleaf
                    )
                    (ℓ "五丌") (ℓ "丌井")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亟") (ℓ "亟亠亘")
                        wleaf
                      )
                      (ℓ "亰亘亝") (ℓ "亝亘")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "举丗") (ℓ "丗举")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨丨亝") (ℓ "丨亝亨")
                        wleaf
                      )
                      (ℓ "乼亚") (ℓ "亞乼")
                      wleaf
                    )
                    (ℓ "乬亢") (ℓ "些乬")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丽与") (ℓ "与丢举")
                        wleaf
                      )
                      (ℓ "云井") (ℓ "井云")
                      wleaf
                    )
                  )
                  (ℓ "乢亡") (ℓ "亡乢")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "举亓") (ℓ "亓举")
                        wleaf
                      )
                      (ℓ "丶亮丶亮丷") (ℓ "亮丶亮丷丶")
                      wleaf
                    )
                    (ℓ "丷乼") (ℓ "乼举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二") (ℓ "亗二亗")
                        wleaf
                      )
                      (ℓ "亜争") (ℓ "争亜")
                      wleaf
                    )
                  )
                )
                (ℓ "亜书") (ℓ "书亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠丌") (ℓ "丌亡亠亠")
                        wleaf
                      )
                      (ℓ "亠乥") (ℓ "乥亜")
                      wleaf
                    )
                    (ℓ "串享") (ℓ "亗串")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亯一下") (ℓ "一下亯")
                        wleaf
                      )
                      (ℓ "丽乕") (ℓ "乕丽")
                      wleaf
                    )
                  )
                  (ℓ "五亖乐亖五乐") (ℓ "亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳井") (ℓ "井乳亡")
                        wleaf
                      )
                      (ℓ "五乪") (ℓ "乪五")
                      wleaf
                    )
                    (ℓ "五並乹並") (ℓ "並乹並五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰举亜举丿亜") (ℓ "丰")
                        wleaf
                      )
                      (ℓ "亃亝亝") (ℓ "亃")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "乖上井下") (ℓ "井五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亇二二") (ℓ "二亇")
                        wleaf
                      )
                      (ℓ "丶亞") (ℓ "亞丶")
                      wleaf
                    )
                    (ℓ "亗亗") []
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亟亟") (ℓ "也")
                        wleaf
                      )
                      (ℓ "乺井") (ℓ "井乺")
                      wleaf
                    )
                  )
                  (ℓ "乬些") (ℓ "亢乬")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠些亜") (ℓ "些亠")
                        wleaf
                      )
                      (ℓ "乄亢") (ℓ "亢乄亮")
                      wleaf
                    )
                    (ℓ "上亝") (ℓ "亝上乩亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亟丱") (ℓ "亟亜")
                        wleaf
                      )
                      (ℓ "亨亞") (ℓ "亞亨五")
                      wleaf
                    )
                  )
                )
                (ℓ "亠") (ℓ "乻亠乻")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜些") (ℓ "些亜")
                        wleaf
                      )
                      (ℓ "五世乪") (ℓ "世乪五")
                      wleaf
                    )
                    (ℓ "串亗") (ℓ "享串")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亗与中与") (ℓ "与中与亗")
                        wleaf
                      )
                      (ℓ "丸亊丸丸") (ℓ "丸亊")
                      wleaf
                    )
                  )
                  (ℓ "买亡") (ℓ "亡买")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世丂世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世丂乇乇乕乕乕亄乕") (ℓ "乕亄亄亨乇乇乇乇乇乇乇丒乇丒乇世世世丂世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世丂乇乇乕乕乕")
                        wleaf
                      )
                      (ℓ "丰书亲") (ℓ "书亲丰")
                      wleaf
                    )
                    (ℓ "亘亞") (ℓ "亞亘亠")
                    (wnode
                      wleaf
                      (ℓ "五买京") (ℓ "买五")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "亡业") (ℓ "业亡")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亢") (ℓ "亢丿亠")
                        wleaf
                      )
                      (ℓ "乽亝") (ℓ "亝乽亙")
                      wleaf
                    )
                    (ℓ "乭二二") (ℓ "乭")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乹亓乹亓乺") (ℓ "亓乹亓乺乹")
                        wleaf
                      )
                      (ℓ "五为") (ℓ "为五")
                      wleaf
                    )
                  )
                  (ℓ "二亃亜") (ℓ "亃二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "串亢") (ℓ "亲串")
                        wleaf
                      )
                      (ℓ "亐五亮丶五亮丷並") (ℓ "五亮丶五亮丷並亐")
                      wleaf
                    )
                    (ℓ "亐五") (ℓ "五亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜") (ℓ "丱亜丱")
                        wleaf
                      )
                      (ℓ "亜丽") (ℓ "丽亜")
                      wleaf
                    )
                  )
                )
                (ℓ "亨") (ℓ "亝亨亝")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐乁") (ℓ "乁亐")
                        wleaf
                      )
                      (ℓ "亡並亊並") (ℓ "並亊並亡")
                      wleaf
                    )
                    (ℓ "乜享") (ℓ "享乜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "些亳") (ℓ "亳亟些")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "亡亰亡")
                      wleaf
                    )
                  )
                  (ℓ "乩亡") (ℓ "亡乩")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五") (ℓ "乒五乒")
                        wleaf
                      )
                      (ℓ "丫亪") (ℓ "亞丫")
                      wleaf
                    )
                    (ℓ "五並乩並") (ℓ "並乩並五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乎亣") (ℓ "亣乎")
                        wleaf
                      )
                      (ℓ "乹亝") (ℓ "亝乹")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "亜亪五") (ℓ "亪亜")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亓亢") (ℓ "亢亓")
                        wleaf
                      )
                      (ℓ "乊亟") (ℓ "亗乊")
                      wleaf
                    )
                    (ℓ "丯亲") (ℓ "亲丯")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丰丢亟丣") (ℓ "亟亜")
                        wleaf
                      )
                      (ℓ "五争") (ℓ "争五")
                      wleaf
                    )
                  )
                  (ℓ "二乭") (ℓ "乭二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亪") (ℓ "亪二五")
                        wleaf
                      )
                      (ℓ "举亪") (ℓ "亪举")
                      wleaf
                    )
                    (ℓ "乕井") (ℓ "井乕")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨之亏") (ℓ "之亏乗五亨")
                        wleaf
                      )
                      (ℓ "丘亇丢") (ℓ "丘亞亜丱亇丱丢")
                      wleaf
                    )
                  )
                )
                (ℓ "亠乕") (ℓ "乕亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠丒") (ℓ "丒亠")
                        wleaf
                      )
                      (ℓ "丞亊丢亮丶亮丷") (ℓ "亮丶亮丷丞亊丢")
                      wleaf
                    )
                    (ℓ "亠亗") (ℓ "亗亠亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乶亟") (ℓ "亟乶亣")
                        wleaf
                      )
                      (ℓ "亁乇") (ℓ "乇亁")
                      wleaf
                    )
                  )
                  (ℓ "丶乹亠乹乻亠") (ℓ "丶")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亂亁") []
                        wleaf
                      )
                      (ℓ "亜乖") (ℓ "乖亜")
                      wleaf
                    )
                    (ℓ "亜不") (ℓ "不亝")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亳亘") (ℓ "亳亜")
                        wleaf
                      )
                      (ℓ "丌丯了丰了丽不") (ℓ "亝")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜丿亞亜") (ℓ "亞")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了些") (ℓ "些了亢")
                        wleaf
                      )
                      (ℓ "丶並亇並") (ℓ "並亇並丶")
                      wleaf
                    )
                    (ℓ "亜乙二") (ℓ "乙亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丢") (ℓ "与丽与丽")
                        wleaf
                      )
                      (ℓ "乳亠亠") (ℓ "乳")
                      wleaf
                    )
                  )
                  (ℓ "亐亓乻亓亐乻") (ℓ "五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亀亱") (ℓ "亱亀")
                        wleaf
                      )
                      (ℓ "亀亮") (ℓ "亮亀")
                      wleaf
                    )
                    (ℓ "丢並丽並") (ℓ "並丽並丢")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五乫") (ℓ "乫五")
                        wleaf
                      )
                      (ℓ "争亜亜") (ℓ "争")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亰") (ℓ "亰亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠井京") (ℓ "井亠")
                        wleaf
                      )
                      (ℓ "上举並") (ℓ "並丽")
                      wleaf
                    )
                    (ℓ "亠") (ℓ "丿亠丿")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜二亗") (ℓ "亗亜")
                        wleaf
                      )
                      (ℓ "丽亭") (ℓ "亭丽")
                      wleaf
                    )
                  )
                  (ℓ "五") (ℓ "亜亞义亞亜义")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亰亡") (ℓ "亡亘")
                        wleaf
                      )
                      (ℓ "二亃") (ℓ "亃亜二")
                      wleaf
                    )
                    (ℓ "亁並亁並") (ℓ "並亁並亁")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亗") (ℓ "亗丨")
                        wleaf
                      )
                      (ℓ "乥亡") (ℓ "亝乥")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五井乗") (ℓ "井五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亀亲亲") (ℓ "亀")
                        wleaf
                      )
                      (ℓ "乘亍") (ℓ "亝乘")
                      wleaf
                    )
                    (ℓ "亠乢") (ℓ "乢亠")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五个亗") (ℓ "亗五")
                        wleaf
                      )
                      (ℓ "亜亍亨") (ℓ "亍亜")
                      wleaf
                    )
                  )
                  (ℓ "亐亠") (ℓ "亠亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五丘") (ℓ "丘五")
                        wleaf
                      )
                      (ℓ "五亮") (ℓ "亮五")
                      wleaf
                    )
                    (ℓ "亜並乕並") (ℓ "並乕並亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰些") (ℓ "些亜亰")
                        wleaf
                      )
                      (ℓ "亃亮丶亮丷") (ℓ "亮丶五亮丷亐亄乕乕亄亐丢丽")
                      wleaf
                    )
                  )
                )
                (ℓ "五亍") (ℓ "亍五亨")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠串") (ℓ "串亰")
                        wleaf
                      )
                      (ℓ "五丒亄丢") (ℓ "丒亄丢五")
                      wleaf
                    )
                    (ℓ "五") (ℓ "丳五丳")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亣") (ℓ "亣亜亘")
                        wleaf
                      )
                      (ℓ "亠东") (ℓ "东亠")
                      wleaf
                    )
                  )
                  (ℓ "二亀亨") (ℓ "亀二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "並亁並並丽並並丽並並亁並並丢並並亁並並丽並並丽並並亁並並丢並") []
                        wleaf
                      )
                      (ℓ "京为") (ℓ "为五京")
                      wleaf
                    )
                    (ℓ "亠乄") (ℓ "乄京亠")
                    (wnode
                      wleaf
                      (ℓ "乭亘亘") (ℓ "乭")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (ℓ "亡亡") []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五丯亪") (ℓ "丯亪五")
                        wleaf
                      )
                      (ℓ "五並亄並") (ℓ "並亄並五")
                      wleaf
                    )
                    (ℓ "亐云丿云亐丿") (ℓ "京")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亓乹五亓乺与京") (ℓ "京五亓乹五亓乺与")
                        wleaf
                      )
                      (ℓ "亜亏") (ℓ "亏亜五")
                      wleaf
                    )
                  )
                  (ℓ "亜") (ℓ "乫亜乫")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丹亳") (ℓ "亟丹")
                        wleaf
                      )
                      (ℓ "乇丌亁丢") (ℓ "丌亁丢乇")
                      wleaf
                    )
                    (ℓ "亨五亨五亨") (ℓ "亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠亯亐") (ℓ "亯亠")
                        wleaf
                      )
                      (ℓ "丽丽丽丽") []
                      wleaf
                    )
                  )
                )
                (ℓ "乩亙") (ℓ "亙乩")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亀亲") (ℓ "亲亀")
                        wleaf
                      )
                      (ℓ "二乬") (ℓ "乬五")
                      wleaf
                    )
                    (ℓ "举丷亠乽") (ℓ "乽举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五丒中上") (ℓ "丒中上五")
                        wleaf
                      )
                      (ℓ "丱亨井") (ℓ "井丱")
                      wleaf
                    )
                  )
                  (ℓ "亠") (ℓ "丶争丷争丽")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丞亞") (ℓ "亞丞")
                        wleaf
                      )
                      (ℓ "亀亪") (ℓ "亪亀")
                      wleaf
                    )
                    (ℓ "丽亞") (ℓ "亞丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "么与丽与") (ℓ "与丽与么")
                        wleaf
                      )
                      (ℓ "乼互") (ℓ "亖乼")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五亜") (ℓ "亜五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亄二並") (ℓ "並二丒亄丢二")
                        wleaf
                      )
                      (ℓ "亘亰") (ℓ "亰亘")
                      wleaf
                    )
                    (ℓ "亰丶") (ℓ "丶亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亟亳") (ℓ "亳亟")
                        wleaf
                      )
                      (ℓ "五亝") (ℓ "亝亨五")
                      wleaf
                    )
                  )
                  (ℓ "二乖") (ℓ "乖二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜乄亨") (ℓ "乄亜")
                        wleaf
                      )
                      (ℓ "丫亣") (ℓ "亯丫")
                      wleaf
                    )
                    (ℓ "举井") (ℓ "井举乖五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯亣") (ℓ "亣丯")
                        wleaf
                      )
                      (ℓ "五亄") (ℓ "个亄个五")
                      wleaf
                    )
                  )
                )
                (ℓ "乕亍") (ℓ "亍乕")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乾亠") (ℓ "亣乾")
                        wleaf
                      )
                      (ℓ "丒亄丢亮丶亮丷") (ℓ "亮丶亮丷丒亄丢")
                      wleaf
                    )
                    (ℓ "两丨亀丩亀乕严") (ℓ "亗")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘") (ℓ "乽亘乽")
                        wleaf
                      )
                      (ℓ "亁亲") (ℓ "亲亁")
                      wleaf
                    )
                  )
                  (ℓ "丶亡") (ℓ "亡丶乹亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亡") (ℓ "亡亰亘")
                        wleaf
                      )
                      (ℓ "丞亝") (ℓ "亝丞")
                      wleaf
                    )
                    (ℓ "乏並亁並") (ℓ "並亁並乏")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "么亟") (ℓ "亟么")
                        wleaf
                      )
                      (ℓ "丽亮") (ℓ "亮丽")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亜丬") (ℓ "丬亜")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亘亲") (ℓ "亲亜亘")
                        wleaf
                      )
                      (ℓ "乩亞") (ℓ "亞乩丽亜")
                      wleaf
                    )
                    (ℓ "亰亙") (ℓ "亙亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜一下") (ℓ "一下亜")
                        wleaf
                      )
                      (ℓ "亜亱") (ℓ "亱亠亜")
                      wleaf
                    )
                  )
                  (ℓ "乘亡") (ℓ "云乘")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亞") (ℓ "亞五")
                        wleaf
                      )
                      (ℓ "乄亮") (ℓ "亮乄")
                      wleaf
                    )
                    (ℓ "亮丶亮丷並丢並") (ℓ "並丢並亮丶亮丷")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丯丽亜丽丿亜") (ℓ "丯")
                        wleaf
                      )
                      (ℓ "亐五亐五亐") (ℓ "亐")
                      wleaf
                    )
                  )
                )
                (ℓ "亜亝") (ℓ "亝乫亜")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亁五亁丢亄五亄丢") (ℓ "井亖")
                        wleaf
                      )
                      (ℓ "亜亞乤亞亜乤") (ℓ "亠")
                      wleaf
                    )
                    (ℓ "亰举") (ℓ "举亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "互亠亠") (ℓ "互")
                        wleaf
                      )
                      (ℓ "亇丽") (ℓ "丽亇")
                      wleaf
                    )
                  )
                  (ℓ "亐") (ℓ "亠亣乗亣亠乗")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乑亣") (ℓ "亗乑")
                        wleaf
                      )
                      (ℓ "亠亲") (ℓ "亲亠亜")
                      wleaf
                    )
                    (ℓ "丽並亁並") (ℓ "並亁並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "举亗") (ℓ "亗举丩五")
                        wleaf
                      )
                      (ℓ "丞亊丢") (ℓ "丞亢亠丸亊丸丢")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五之") (ℓ "之五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乁亐亐") (ℓ "乁")
                        wleaf
                      )
                      (ℓ "亠乙") (ℓ "乙亐亠")
                      wleaf
                    )
                    (ℓ "五亍亨") (ℓ "亍五")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "为亳") (ℓ "亳为亟")
                        wleaf
                      )
                      (ℓ "亨井") (ℓ "井亨")
                      wleaf
                    )
                  )
                  (ℓ "亐亃亠") (ℓ "亃亐")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "京举") (ℓ "举京")
                        wleaf
                      )
                      (ℓ "亜亨亜亨亜") (ℓ "亜")
                      wleaf
                    )
                    (ℓ "乇並丽並") (ℓ "並丽並乇")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亣亳") (ℓ "亳亣")
                        wleaf
                      )
                      (ℓ "乽亚亚") (ℓ "乽")
                      wleaf
                    )
                  )
                )
                (ℓ "亠亡") (ℓ "亡亠乻")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亐亢五") (ℓ "亢亐")
                        wleaf
                      )
                      (ℓ "丌亁丢亲") (ℓ "亲丌亁丢")
                      wleaf
                    )
                    (ℓ "二享") (ℓ "享二")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨亯") (ℓ "亯丨")
                        wleaf
                      )
                      (ℓ "个亝") (ℓ "亝个亨")
                      wleaf
                    )
                  )
                  (ℓ "举乺亠乺乻亠") (ℓ "举")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕亄亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕") (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕亄亄五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕")
                        wleaf
                      )
                      (ℓ "买亰亰") (ℓ "买")
                      wleaf
                    )
                    (ℓ "亃亞") (ℓ "亞亃")
                    (wnode
                      wleaf
                      (ℓ "京丹") (ℓ "丹五")
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (ℓ "丘亜丙") (ℓ "亞")
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丙亢") (ℓ "亢丙")
                        wleaf
                      )
                      (ℓ "乽亙亙") (ℓ "乽")
                      wleaf
                    )
                    (ℓ "乽亙") (ℓ "亙乽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丒中上亓乹亓乺") (ℓ "亓乹亓乺丒中上")
                        wleaf
                      )
                      (ℓ "亜") (ℓ "丿亜丿")
                      wleaf
                    )
                  )
                  (ℓ "二亜") (ℓ "亜二")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亰亞亠") (ℓ "亞亰")
                        wleaf
                      )
                      (ℓ "亜亪") (ℓ "亪五亜")
                      wleaf
                    )
                    (ℓ "五乼") (ℓ "乼亐")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠互") (ℓ "互亠")
                        wleaf
                      )
                      (ℓ "乕亮丶亮丷") (ℓ "亮丶亮丷乕")
                      wleaf
                    )
                  )
                )
                (ℓ "丌亜不") (ℓ "亝")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨二亨二亨") (ℓ "亨")
                        wleaf
                      )
                      (ℓ "乕亝") (ℓ "亝乕")
                      wleaf
                    )
                    (ℓ "乄享") (ℓ "享乄")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "五亟") (ℓ "亟二五")
                        wleaf
                      )
                      (ℓ "亰") (ℓ "买亰买")
                      wleaf
                    )
                  )
                  (ℓ "五乑") (ℓ "乑亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠乒") (ℓ "乒五亠")
                        wleaf
                      )
                      (ℓ "乶亠亠") (ℓ "乶")
                      wleaf
                    )
                    (ℓ "丽並乹並") (ℓ "並乹並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乳互亓乹亓乺") (ℓ "亓乹亓乺乳互")
                        wleaf
                      )
                      (ℓ "乙亍") (ℓ "亍乙")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五") (ℓ "丽乙举乙丨")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亃亓") (ℓ "亓亃亢")
                        wleaf
                      )
                      (ℓ "亁並亊並") (ℓ "並亊並亁")
                      wleaf
                    )
                    (ℓ "亰丽") (ℓ "丽亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "也亗") (ℓ "亗也亟")
                        wleaf
                      )
                      (ℓ "亘亲亜") (ℓ "亲亘")
                      wleaf
                    )
                  )
                  (ℓ "乭亙亙") (ℓ "乭")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丬亜亜") (ℓ "丬")
                        wleaf
                      )
                      (ℓ "五亪") (ℓ "亪五")
                      wleaf
                    )
                    (ℓ "乏並丽並") (ℓ "並丽並乏")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亨之亏乗五") (ℓ "之亏亨")
                        wleaf
                      )
                      (ℓ "乁亚") (ℓ "亚乁")
                      wleaf
                    )
                  )
                )
                (ℓ "书亜亜") (ℓ "书")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亠些") (ℓ "些亠")
                        wleaf
                      )
                      (ℓ "乏上举") (ℓ "上举乏")
                      wleaf
                    )
                    (ℓ "亰乜") (ℓ "乜亰")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乶亣亣") (ℓ "乶")
                        wleaf
                      )
                      (ℓ "亇丶") (ℓ "丶亇")
                      wleaf
                    )
                  )
                  (ℓ "丸亡") (ℓ "亡丸乻")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丨") (ℓ "亮丶丨五亮丷亮丶亮丷")
                        wleaf
                      )
                      (ℓ "二亪五") (ℓ "亪二")
                      wleaf
                    )
                    (ℓ "丽並亄並") (ℓ "並亄並丽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "主与丽与") (ℓ "与丽与主")
                        wleaf
                      )
                      (ℓ "乩些") (ℓ "些乩")
                      wleaf
                    )
                  )
                )
              )
            )
            (ℓ "亐五亮") (ℓ "亮亐")
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "了亢亢") (ℓ "了")
                        wleaf
                      )
                      (ℓ "亐井") (ℓ "井亐京")
                      wleaf
                    )
                    (ℓ "乽云") (ℓ "云乽")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜丱亟亜") (ℓ "亟")
                        wleaf
                      )
                      (ℓ "並丸丸") (ℓ "並")
                      wleaf
                    )
                  )
                  (ℓ "五乗井") (ℓ "井五")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亱亢") (ℓ "亢亞亱")
                        wleaf
                      )
                      (ℓ "亜") (ℓ "丬亜丬")
                      wleaf
                    )
                    (ℓ "乹並丽並") (ℓ "並丽並乹")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠些") (ℓ "些亜亠")
                        wleaf
                      )
                      (ℓ "亜丌") (ℓ "丌亝亜亜")
                      wleaf
                    )
                  )
                )
                (ℓ "乺云") (ℓ "云乺")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜") (ℓ "亄五亄丢亨亄五亄丢亨")
                        wleaf
                      )
                      (ℓ "丷世乪") (ℓ "世乪丷")
                      wleaf
                    )
                    (ℓ "举么") (ℓ "么举")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜亣亘") (ℓ "亣亜")
                        wleaf
                      )
                      (ℓ "亁乩") (ℓ "乩亁")
                      wleaf
                    )
                  )
                  (ℓ "亠上") (ℓ "上亠")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "井亮") (ℓ "亮井")
                        wleaf
                      )
                      (ℓ "亠乏") (ℓ "乏亠")
                      wleaf
                    )
                    (ℓ "亜並亁並") (ℓ "並亁並亜")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乏与丽与") (ℓ "与丽与乏")
                        wleaf
                      )
                      (ℓ "亐亮五") (ℓ "亮亐")
                      wleaf
                    )
                  )
                )
              )
              (ℓ "五乩") (ℓ "乩五")
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二乁") (ℓ "乁二")
                        wleaf
                      )
                      (ℓ "亘乺") (ℓ "乺亘")
                      wleaf
                    )
                    (ℓ "亨举") (ℓ "举亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "丟亗") (ℓ "亗丟")
                        wleaf
                      )
                      (ℓ "亐並") (ℓ "並亐")
                      wleaf
                    )
                  )
                  (ℓ "乢亝") (ℓ "亝乢")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亠京云") (ℓ "云亠")
                        wleaf
                      )
                      (ℓ "亠亮五") (ℓ "亮亠")
                      wleaf
                    )
                    (ℓ "云並乕並") (ℓ "並乕並云")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "举亟") (ℓ "亟举丰亜")
                        wleaf
                      )
                      (ℓ "亐乼") (ℓ "乼五")
                      wleaf
                    )
                  )
                )
                (ℓ "亠亙亰") (ℓ "亙亠")
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "二亞") (ℓ "亞二五")
                        wleaf
                      )
                      (ℓ "云一丣") (ℓ "一丣云")
                      wleaf
                    )
                    (ℓ "亨丳") (ℓ "丳五亨")
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "乄亯亯") (ℓ "乄")
                        wleaf
                      )
                      (ℓ "亟乕亟乖") (ℓ "享丽享举")
                      wleaf
                    )
                  )
                  (ℓ "亀亨亨") (ℓ "亀")
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (ℓ "亜与上与") (ℓ "与上与亜")
                        wleaf
                      )
                      (ℓ "亜") (ℓ "亰亲丸亲亰丸")
                      wleaf
                    )
                    (ℓ "丫亞") (ℓ "亪丫")
                    (wnode
                      wleaf
                      (ℓ "二了") (ℓ "了五二")
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

WsL : Set
WsL = WProofs windowsL

record Ws : Set where
  no-eta-equality
  field
    lit : WsL
    pl  : WProofs windowsP

open Ws public using (lit)

-- The n-th literal and placed windows.
wl : (n : ℕ) → WsL → WinT windowsL n
wl n W = wget windowsL W n

wp : (n : ℕ) → Ws → WinT windowsP n
wp n W = wget windowsP (Ws.pl W) n
